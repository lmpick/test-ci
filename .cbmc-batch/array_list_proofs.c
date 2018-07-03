#include <aws/common/array_list.h>
#include <assert.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <proof_helpers.h>

#define MAX_INITIAL_ITEM_ALLOCATION 2
#define MAX_ITEM_SIZE 15

void aws_array_list_init_dynamic_verify(struct aws_array_list *list, struct aws_allocator *allocator,
    size_t initial_item_allocation, size_t item_size) {
    list = malloc(sizeof(*list));
    allocator = malloc(sizeof(*allocator));

    // assume the allocator is indistinguishable from default
    aws_allocator_assumptions(allocator);

    aws_array_list_init_dynamic(list, allocator, initial_item_allocation, item_size);
    
    // some guarantees
    assert(list->alloc == allocator);
    assert(list->item_size == item_size);
    __CPROVER_assume(initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION && item_size <= MAX_ITEM_SIZE);
    assert(list->data == NULL || list->current_size == (initial_item_allocation * item_size));
}

void aws_array_list_init_static_verify(struct aws_array_list *list, void *raw_array,
    size_t initial_item_allocation, size_t item_size) {
    list = malloc(sizeof(*list));
    size_t len = nondet_size_t();
    raw_array = malloc(len);

    __CPROVER_assume(initial_item_allocation > 0);
    __CPROVER_assume(item_size > 0);

    aws_array_list_init_static(list, raw_array, initial_item_allocation, item_size);
    
    // some guarantees
    assert(list->alloc == NULL);
    assert(list->item_size == item_size);
    assert(list->data == raw_array);
}

void aws_array_list_set_at_verify(struct aws_array_list* list, void *val, size_t index) {

    size_t initial_item_allocation = nondet_size_t(0);
    size_t item_size = nondet_size_t(1);
    __CPROVER_assume(initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
	__CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    list = get_arbitrary_array_list(initial_item_allocation, item_size);

    val = malloc(item_size);

    __CPROVER_assume(index < __CPROVER_constant_infinity_uint - 1);
    
    aws_array_list_set_at(list, val, index);
}

void aws_array_list_push_back_verify(void) {
    size_t initial_item_allocation = nondet_size_t(0);
    size_t item_size = nondet_size_t(1);
    __CPROVER_assume(initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
	__CPROVER_assume(item_size <= MAX_ITEM_SIZE);

    struct aws_array_list* list = get_arbitrary_array_list(initial_item_allocation, item_size);

    void *val = malloc(item_size);
    aws_array_list_push_back(list, val);
}
