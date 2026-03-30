/*
 * lru.c - LRU cache implementation
 * Copyright (c) 2016,2020 Red Hat Inc.
 * All Rights Reserved.
 *
 * This software may be freely redistributed and/or modified under the
 * terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 2, or (at your option) any
 * later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; see the file COPYING. If not, write to the
 * Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor
 * Boston, MA 02110-1335, USA.
 *
 * Authors:
 *   Steve Grubb <sgrubb@redhat.com>
 */

#include "config.h"
#include <stdlib.h>
#include <string.h>
#include "lru.h"
#include "message.h"
#include "gcc-attributes.h"

//#define DEBUG

// Local declarations
static void dequeue(Queue *queue);
static QNode *qnode_alloc(Queue *queue);
static void qnode_free(Queue *queue, QNode *node);
static QNode *hash_find(Hash *hash, unsigned int slot, unsigned int key);
static void hash_remove(Hash *hash, unsigned int slot, QNode *node);
static void hash_insert(Hash *hash, unsigned int slot, QNode *node);
static Hash *create_hash(unsigned int hsize)
{
	unsigned int i;

	Hash *hash = malloc(sizeof(Hash));
	if (hash == NULL)
		return hash;

	hash->array = malloc(hsize * sizeof(QNode*));
	if (hash->array == NULL) {
		free(hash);
		return NULL;
	}

	// Initialize all hash entries as empty
	for (i = 0; i < hsize; i++)
		hash->array[i] = NULL;

	hash->size = hsize;
	return hash;
}

/*
 * qnode_alloc - get a QNode from the pre-allocated pool
 * @queue: queue managing the pool
 */
static QNode *qnode_alloc(Queue *queue)
{
	QNode *node;

	if (queue == NULL)
		return NULL;

	node = queue->free_list;
	if (node == NULL)
		return NULL;

	queue->free_list = node->next;
	node->prev = NULL;
	node->next = NULL;
	node->hash_next = NULL;
	node->key = 0;
	node->item = NULL;
	node->uses = 1; // Setting to 1 because its being used

	return node;
}

/*
 * qnode_free - return a QNode to the pre-allocated pool
 * @queue: queue managing the pool
 * @node: node to return
 */
static void qnode_free(Queue *queue, QNode *node)
{
	if (queue == NULL || node == NULL)
		return;

	node->item = NULL;
	node->uses = 0;
	node->key = 0;
	node->prev = NULL;
	node->next = queue->free_list;
	node->hash_next = NULL;
	queue->free_list = node;
}

static void dump_queue_stats(const Queue *q)
{
	msg(LOG_DEBUG, "%s cache size: %u", q->name, q->total);
	msg(LOG_DEBUG, "%s slots in use: %u (%u%%)", q->name, q->count,
				q->total ? (100*q->count)/q->total : 0);
	msg(LOG_DEBUG, "%s hits: %lu", q->name, q->hits);
	msg(LOG_DEBUG, "%s misses: %lu", q->name, q->misses);
	msg(LOG_DEBUG, "%s evictions: %lu (%lu%%)", q->name, q->evictions,
				q->hits ? (100*q->evictions)/q->hits : 0);
}

static Queue *create_queue(unsigned int qsize, const char *name)
{
	unsigned int i;

	Queue *queue = malloc(sizeof(Queue));
	if (queue == NULL)
		return queue;

	// The queue is empty
	queue->count = 0;
	queue->hits = 0;
	queue->misses = 0;
	queue->evictions = 0;
	queue->front = queue->end = NULL;

	// Number of slots that can be stored in memory
	queue->total = qsize;

	queue->name = name;

	queue->cleanup = NULL;
	queue->evict_cb = NULL;
	queue->free_list = NULL;
	queue->pool = malloc(qsize * sizeof(QNode));
	if (queue->pool == NULL) {
		free(queue);
		return NULL;
	}

	for (i = 0; i < qsize; i++)
		qnode_free(queue, &queue->pool[i]);

	return queue;
}

static void destroy_queue(Queue *queue)
{
	dump_queue_stats(queue);

	// Some static analysis scanners try to flag this as a use after
	// free accessing queue->end. This is a false positive. It is freed.
	// However, static analysis apps are incapable of seeing that in
	// remove_node, end is updated to a prior node as part of detaching
	// the current end node.
	while (queue->count)
		dequeue(queue);

	free(queue->pool);
	free(queue->hash->array);
	free(queue->hash);
	free(queue);
}

static unsigned int are_all_slots_full(const Queue *queue)
{
	return queue->count == queue->total;
}

static unsigned int queue_is_empty(const Queue *queue)
{
	return queue->end == NULL;
}

#ifdef DEBUG
static void sanity_check_queue(Queue *q, const char *id)
{
	unsigned int i;
	QNode *n;

	if (q == NULL) {
		msg(LOG_DEBUG, "%s - q is NULL", id);
		abort();
	}

	n = q->front;
	if (n == NULL)
		return;

	// Walk bottom to top
	i = 0;
	while (n->next) {
		if (n->next->prev != n) {
			msg(LOG_DEBUG, "%s - corruption found %u", id, i);
			abort();
		}
		if (i == q->count) {
			msg(LOG_DEBUG, "%s - forward loop found %u", id, i);
			abort();
		}
		i++;
		n = n->next;
	}

	// Walk top to bottom
	n = q->end;
	while (n->prev) {
		if (n->prev->next != n) {
			msg(LOG_DEBUG, "%s - Corruption found %u", id, i);
			abort();
		}
		if (i == 0) {
			msg(LOG_DEBUG, "%s - backward loop found %u", id, i);
			abort();
		}
		i--;
		n = n->prev;
	}
}
#else
#define sanity_check_queue(a, b) do {} while(0)
#endif

static void insert_before(Queue *queue, QNode *node, QNode *new_node)
{
	sanity_check_queue(queue, "1 insert_before");
	if (queue == NULL || node == NULL || new_node == NULL)
		return;
	new_node->prev = node->prev;
	new_node->next  = node;
	if (node->prev == NULL)
		queue->front = new_node;
	else
		node->prev->next = new_node;
	node->prev = new_node;
	sanity_check_queue(queue, "2 insert_before");
}

static void insert_beginning(Queue *queue, QNode *new_node)
{
	sanity_check_queue(queue, "1 insert_beginning");
	if (queue == NULL || new_node == NULL)
		return;
	if (queue->front == NULL) {
		queue->front = new_node;
		queue->end = new_node;
		new_node->prev = NULL;
		new_node->next = NULL;
	} else
		insert_before(queue, queue->front, new_node);
	sanity_check_queue(queue, "2 insert_beginning");
}

static void remove_node(Queue *queue, const QNode *node)
{
	// If we are at the beginning
	sanity_check_queue(queue, "1 remove_node");
	if (node->prev == NULL) {
		queue->front = node->next;
		if (queue->front)
			queue->front->prev = NULL;
		goto out;
	} else {
		if (node->prev->next != node) {
			msg(LOG_ERR, "Linked list corruption detected %s",
				queue->name);
			abort();
		}
		node->prev->next = node->next;
	}

	// If we are at the end
	if (node->next == NULL) {
		queue->end = node->prev;
		if (queue->end)
			queue->end->next = NULL;
	} else {
		if (node->next->prev != node) {
			msg(LOG_ERR, "Linked List corruption detected %s",
				queue->name);
			abort();
		}
		node->next->prev = node->prev;
	}
out:
	sanity_check_queue(queue, "2 remove_node");
}

// Remove from the end of the queue
static void dequeue(Queue *queue)
{
	if (queue_is_empty(queue))
		return;

	QNode *temp = queue->end;
	unsigned int slot = temp->key % queue->hash->size;

	// Remove from hash chain
	hash_remove(queue->hash, slot, temp);
	remove_node(queue, queue->end);

	// Let caller know an entry is being evicted
	if (queue->evict_cb)
		queue->evict_cb(temp->item);
	queue->cleanup(temp->item);
	free(temp->item);
	qnode_free(queue, temp);

	// decrement the total of full slots by 1
	queue->count--;
}

/*
 * hash_find - find a node in the hash chain with the given key
 * @hash: hash table
 * @slot: hash slot index
 * @key:  key to search for
 *
 * Returns the node if found, NULL otherwise.
 */
static QNode *hash_find(Hash *hash, unsigned int slot, unsigned int key)
{
	QNode *node = hash->array[slot];

	while (node) {
		if (node->key == key)
			return node;
		node = node->hash_next;
	}

	return NULL;
}

/*
 * hash_remove - remove a node from its hash chain
 * @hash: hash table
 * @slot: hash slot index
 * @node: node to remove
 */
static void hash_remove(Hash *hash, unsigned int slot, QNode *node)
{
	QNode *curr = hash->array[slot];
	QNode *prev = NULL;

	while (curr) {
		if (curr == node) {
			if (prev)
				prev->hash_next = node->hash_next;
			else
				hash->array[slot] = node->hash_next;
			node->hash_next = NULL;
			return;
		}
		prev = curr;
		curr = curr->hash_next;
	}
}

/*
 * hash_insert - insert a node at the head of a hash chain
 * @hash: hash table
 * @slot: hash slot index
 * @node: node to insert
 */
static void hash_insert(Hash *hash, unsigned int slot, QNode *node)
{
	node->hash_next = hash->array[slot];
	hash->array[slot] = node;
}

/*
 * lru_evict - remove the cache entry that should be at the front of the
 *             queue
 * @queue: pointer to the LRU queue
 * @key:   hash index for the entry to evict
 *
 * The caller must first move the desired entry to the front of the queue by
 * calling check_lru_cache() with the same key. This ensures that @key refers
 * to the front node. If the node at the front does not match @key, the
 * program will abort as this is a usage error.
 */
void lru_evict(Queue *queue, unsigned int key)
{
	if (queue_is_empty(queue))
		return;

	Hash *hash = queue->hash;
	QNode *temp = queue->front;
	unsigned int slot = key % hash->size;

	if (temp->key != key) {
		msg(LOG_ERR, "lru_evict called with mismatched key %s (expected %u, got %u)",
			queue->name, key, temp->key);
		abort();
	}

	// Remove from hash chain
	hash_remove(hash, slot, temp);
	remove_node(queue, queue->front);

	// Let caller know an entry is being evicted
	if (queue->evict_cb)
		queue->evict_cb(temp->item);
	queue->cleanup(temp->item);
	free(temp->item);
	qnode_free(queue, temp);

	// decrement the total of full slots by 1
	queue->count--;
	queue->evictions++;
}

// Make a new entry with item to be assigned later
// and setup the hash key
static void enqueue(Queue *queue, unsigned int key)
{
	QNode *temp;
	Hash *hash = queue->hash;
	unsigned int slot = key % hash->size;

	// If all slots are full, remove the page at the end
	if (are_all_slots_full(queue)) {
		dequeue(queue);
	}

	// Create a new node with given page total,
	// And add the new node to the front of queue
	temp = qnode_alloc(queue);
	if (temp == NULL) {
		msg(LOG_ERR, "Unable to allocate node for %s", queue->name);
		return;
	}

	temp->key = key;
	insert_beginning(queue, temp);
	hash_insert(hash, slot, temp);

	// increment number of full slots
	queue->count++;
}

// This function is called needing an item from cache.
//  There are two scenarios:
// 1. Item is not in cache, so add it to the front of the queue
// 2. Item is in cache, we move the item to front of queue
QNode *check_lru_cache(Queue *queue, unsigned int key)
{
	QNode *reqPage;
	Hash *hash = queue->hash;
	unsigned int slot = key % hash->size;

	// Search the hash chain for the matching key
	reqPage = hash_find(hash, slot, key);

	// item is not in cache, make new spot for it
	if (reqPage == NULL) {
		enqueue(queue, key);
		queue->misses++;

	// item is there but not at front. Move it
	} else if (reqPage != queue->front) {
		remove_node(queue, reqPage);
		reqPage->next = NULL;
		reqPage->prev = NULL;
		insert_beginning(queue, reqPage);

		// Increment cached object metrics
		queue->front->uses++;
		queue->hits++;
	} else
		queue->hits++;

	return queue->front;
}

Queue *init_lru(unsigned int qsize, void (*cleanup)(void *),
		const char *name, void (*evict_cb)(void *))
{
	Queue *q = create_queue(qsize, name);
	if (q == NULL)
		return q;

	q->cleanup = cleanup;
	q->evict_cb = evict_cb;
	q->hash = create_hash(qsize);

	return q;
}

void destroy_lru(Queue *queue)
{
	if (queue == NULL)
		return;

	destroy_queue(queue);
}

unsigned int compute_subject_key(const Queue *queue, unsigned int pid)
{
	// With chained hashing, return the full PID as the key
	// The slot will be computed internally as key % hash_size
	(void)queue;
	return pid;
}

unsigned long compute_object_key(const Queue *queue, unsigned long num)
{
	// With chained hashing, return the full magic number as the key
	// The slot will be computed internally as key % hash_size
	(void)queue;
	return num;
}
