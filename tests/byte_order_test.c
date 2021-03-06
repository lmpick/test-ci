/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/byte_order.h>
#include <aws/testing/aws_test_harness.h>

static int byte_swap_test_fn(struct aws_allocator *alloc, void *ctx) {
    uint64_t ans_x = 0x1122334455667788ULL;
    uint32_t ans_y = 0xaabbccdd;
    uint16_t ans_z = 0xeeff;

    uint8_t x[] = {0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88};
    uint8_t y[] = {0xaa, 0xbb, 0xcc, 0xdd};
    uint8_t z[] = {0xee, 0xff};

    uint64_t x64;
    uint32_t y32;
    uint16_t z16;

    memcpy(&x64, x, sizeof(x64));
    memcpy(&y32, y, sizeof(y32));
    memcpy(&z16, z, sizeof(z16));

    ASSERT_UINT_EQUALS(aws_ntoh64(x64), ans_x);
    ASSERT_UINT_EQUALS(aws_hton64(x64), ans_x);

    ASSERT_UINT_EQUALS(aws_ntoh32(y32), ans_y);
    ASSERT_UINT_EQUALS(aws_hton32(y32), ans_y);

    ASSERT_UINT_EQUALS(aws_ntoh16(z16), ans_z);
    ASSERT_UINT_EQUALS(aws_hton16(z16), ans_z);

    return 0;
}
AWS_TEST_CASE(byte_swap_test, byte_swap_test_fn);
