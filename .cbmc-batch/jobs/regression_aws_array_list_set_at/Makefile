include ../Makefile

proofs.goto:
	cd ../../..; \
    patch source/array_list.c .cbmc-batch/patches/array_list.patch; \
	goto-cc .cbmc-batch/array_list_proofs.c source/byte_buf.c \
	source/array_list.c source/common.c source/error.c -Iinclude/ \
	-I.cbmc-batch/ -o .cbmc-batch/jobs/regression_aws_array_list_set_at/proofs.goto \
	--function aws_array_list_set_at_verify
