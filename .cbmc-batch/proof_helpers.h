#include <aws/common/array_list.h>
#include <assert.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#define MAX_ITEM_SIZE 17
#define MAX_STR_LEN 32
#define MAX_BUF_LEN 32

size_t nondet_size_t();
char nondet_char();
int nondet_int();
char nondet_char();

inline void aws_allocator_assumptions(struct aws_allocator *allocator)
{
    // assume that the allocators' mem_acquire function is indistinguishable from default to the caller
    __CPROVER_assume(allocator->mem_acquire == aws_default_allocator()->mem_acquire);
    // assume that the allocators' mem_release function is indistinguishable from default to the caller
    __CPROVER_assume(allocator->mem_release == aws_default_allocator()->mem_release);
}

struct aws_array_list *get_arbitrary_array_list(size_t initial_item_allocation, size_t item_size) {
    // need list to be a valid pointer, so just allocate it
    // in the future, use __CPROVER_assume(!__CPROVER_invalid_pointer(list));
    struct aws_array_list *list = malloc(sizeof(*list));

    if (nondet_int(-1)) {
        // need allocator to be a valid pointer distinct from the list, so just allocate it
        // in the future, use __CPROVER_assume(!__CPROVER_invalid_pointer(allocator));
        struct aws_allocator *allocator = malloc(sizeof(*allocator));

        // assume the allocator is indistinguishable from default
        aws_allocator_assumptions(allocator);

        aws_array_list_init_dynamic(list, allocator, initial_item_allocation, item_size);
    } else {
        __CPROVER_assume(initial_item_allocation > 0);
        __CPROVER_assume(item_size > 0);

        // need raw array be a valid pointer distinct from the list, so just allocate it
        size_t len = initial_item_allocation * item_size;
        void *raw_array = malloc(len);

        aws_array_list_init_static(list, raw_array, initial_item_allocation, item_size);
    }

    return list;
}
