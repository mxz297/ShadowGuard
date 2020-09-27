#!/bin/bash

bench=$*

root=$LITECFI_HOME

dyninst_lib=$root/thirdparty/dyninst/install/lib

LD_PRELOAD=$root/bazel-bin/src/libstackrt.so:$root/thirdparty/dyninst/install/lib/libdyninstAPI_RT.so $bench
