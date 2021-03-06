## AWS C Common

Core c99 package for AWS SDK for C. Includes cross-platform primitives, configuration, data structures, and error handling.

## License

This library is licensed under the Apache 2.0 License. 

## Usage
### Building
aws-c-common uses CMake for setting up build environments. This library has no non-kernel dependencies so the build is quite
simple. 

For example:

    git clone git@github.com:awslabs/aws-c-common.git aws-c-common
    mkdir aws-c-common-build
    cd aws-c-common-build
    cmake ../aws-c-common
    make -j 12
    make test
    sudo make install
    
Keep in mind that CMake supports multiple build systems, so for each platform you can pass your own build system
as the `-G` option. For example:        

    cmake -GNinja ../aws-c-common
    ninja build
    ninja test
    sudo ninja install
    
Or on windows,     

    cmake -G "Visual Studio 14 2015 Win64" ../aws-c-common
    msbuild.exe ALL_BUILD.vcproj    
    
### API style and conventions
Every API has a specific set of styles and conventions. We'll outline them here. These conventions are followed in every
library in the AWS C SDK ecosystem.

#### Error handling
Every function that returns an `int` type, returns `AWS_OP_SUCCESS` ( 0 ) or `AWS_OP_ERR` (-1) on failure. To retrieve
the error code, use the function `aws_last_error()`. Each error code also has a corresponding error string that can be 
accessed via the `aws_error_str()` function.

In addition, you can install both a global and a thread local error handler by using the `aws_set_global_error_handler_fn()`
and `aws_set_thread_local_error_handler_fn()` functions.

All error functions are in the `include/aws/common/error.h` header file.

#### Naming
Any function that allocates and initializes an object will be suffixed with `new`. Similarly, these objects will always 
have a corresponding function with a `destroy` suffix. The `new` suffixed functions will return `NULL` on failure. 
To respond to the error, call `aws_last_error()`.

Any function that simply initializes an object will be suffixed with `init`. These objects will have a corresponding 
`clean_up` function. In these cases, you are responsible for making the decisions for how your object is allocated.

## Contributing

If you are contributing to this code-base, first off, THANK YOU!. There are a few things to keep in mind to minimize the 
pull request turn around time.

### Coding "guidelines"
These "guidelines" are followed in every library in the AWS C SDK ecosystem.

#### Memory Management
* All APIs that need to be able to allocate memory, must take an instance of `aws_allocator` and use that. No `malloc()` or
`free()` calls should be made directly.
* If an API does not allocate the memory, it does not free it. All allocations and deallocations should take place at the same level.
For example, if a user allocates memory, the user is responsible for freeing it. There will inevitably be a few exceptions to this
rule, but they will need significant justification to make it through the code-review.
* All functions that allocate memory must raise an `AWS_ERROR_OOM` error code upon allocation failures. If it is a `new()` function
it should return NULL. If it is an `init()` function, it should return `AWS_OP_ERR`.

#### Threading
* Occasionally a thread is necessary. In those cases, prefer for memory not to be shared between threads. If memory must cross
a thread barrier it should be a complete ownership hand-off. Bias towards, "if I need a mutex, I'm doing it wrong".
* Do not sleep or block .... ever .... under any circumstances, in non-test-code. 
* Do not expose blocking APIs.

### Error Handling
* For APIs returning an `int` error code. The only acceptable return types are `AWS_OP_SUCCESS` and `AWS_OP_ERR`. Before
returning control to the caller, if you have an error to raise, use the `aws_raise_error()` function.
* For APIs returning an allocated instance of an object, return the memory on success, and `NULL` on failure. Before
returning control to the caller, if you have an error to raise, use the `aws_raise_error()` function.

#### Error Codes
The error handling infrastructure is designed to support multiple libraries. For this to work, AWS maintained libraries 
have pre-slotted error codes for each library. The currently allocated error ranges are:

| Range | Library Name |
| --- | --- |
| [0, 0x0400) | aws-c-common |
| [0x0400, 0x0800) | aws-c-io |
| [0x0800, 0x1000) | aws-c-http |
| [0x1000, 0x2000) |aws-c-eventstream | 
| [0x2000, 0x2800) | (reserved for future project) |

Each library should begin its error codes at the beginning of its range and follow in sequence (don't skip codes). Upon
adding an AWS maintained library, an error code range must be approved and added to the above table.

### Testing
We have a high bar for test coverage, and PRs fixing bugs or introducing new functionality need to have tests before 
they will be accepted. A couple of tips:

#### Aws Test Harness
We provide a test harness for writing unit tests. This includes an allocator that will fail your test if you have any 
memory leaks, as well as some `ASSERT` macros. To write a test:

* Create a *.c test file in the tests directory of the project. 
* Implement one or more tests with the signature `int test_case_name(struct aws_allocator *, void *ctx)`
* Use the `AWS_TEST_CASE` macro to declare the test.
* Include your test in the `tests/main.c` file.
* Include yur test in the `tests/CMakeLists.txt` file. 

### Coding Style
* No Tabs
* Indent is 4 spaces
* K & R style for braces
* Space after if, before the `(`
* Avoid C99 features in header files
* Avoid C++ style comments e.g. `//`
* All public API functions need C++ guards and Windows dll semantics
* Use Unix line endings
* SNAKE_UPPER_CASE constants, macros, and enum members.
* snake_lower_case everything else.
* do not use typedef struct idiom.
* typedef function pointer definitions if you intend to expose them to the user
* typedef enums
* every source and header file must have a copyright header (The standard AWS one for apache 2).
* Use standard include guards (e.g. #IFNDEF HEADER_NAME #define HEADER_NAME etc...)
* Platform specifics should be handled in c files and partitioned by directory.
* namespace all definitions in header files with `aws_<libname>?_<api>_<what it does>`. Lib name is 
not always required if a conflict is not likely and it provides better ergonomics.
* Avoid c-strings, and don't write code that depends on `NULL` terminators. Expose `struct aws_byte_buf` APIs
and let the user figure it out.
* There is only one valid character encoding-- UTF-8. Try not to ever need to care about character encodings, but
where you do, the working assumption should always be UTF-8 unless it's something we don't get a choice in (e.g. a protocol
explicitly mandates a character set).
* If you are adding/using a compiler specific keyword, macro, or intrinsic, hide it behind a platform independent macro
definition. This mainly applies to header files. Obviously, if you are writing a file that will only be built on a certain
platform, you have more liberty on this.



