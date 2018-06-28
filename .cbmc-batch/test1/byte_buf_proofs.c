#include <aws/common/byte_buf.h>
#include <assert.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#define MAX_STR_LEN 32
#define MAX_BUF_LEN 32

inline void aws_allocator_assumptions(struct aws_allocator *allocator)
{
    // assume that the allocators' mem_acquire function is indistinguishable from default to the caller
    __CPROVER_assume(allocator->mem_acquire == aws_default_allocator()->mem_acquire);
    // assume that the allocators' mem_release function is indistinguishable from default to the caller
    __CPROVER_assume(allocator->mem_release == aws_default_allocator()->mem_release);
}


void aws_byte_buf_init_verify(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t len) {
    allocator = malloc(sizeof(*allocator));
    buf = malloc(sizeof(*buf));

    // assume the allocator is indistinguishable from default
    aws_allocator_assumptions(allocator);

    aws_byte_buf_init(allocator, buf, len);
}

void aws_byte_buf_from_c_str_verify(char *c_str) {

    size_t len = nondet_size_t();

    // need c_str to be a valid pointer of size len * sizeof(char)
    c_str = malloc(len * sizeof(*c_str));

    // need *c_str to be a '\0'-terminated C string, so assume an arbitrary character
    // within the array is 0
    uint8_t index = nondet_int();
    __CPROVER_assume(index >= 0 && index < len);
    c_str[index] = 0;
    __CPROVER_assume(len < MAX_STR_LEN);

    aws_byte_buf_from_c_str(c_str);
}
