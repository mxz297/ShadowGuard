
cc_binary(
    name = "cfi",
    srcs = [
	"assembler.cc",
	"assembler.h",
        "cfi.cc",
	"codegen.cc",
	"codegen.h",
	"heap.h",
	"instrument.cc",
	"instrument.h",
        "jit.cc",
	"jit.h",
	"parse.cc",
	"parse.h",
        "passes.h",
        "pass_manager.h",
	"register_utils.h",
	"utils.cc",
	"utils.h",
    ],
    deps = [
       	"@asmjit//:asmjit",
        "@com_github_gflags_gflags//:gflags",
       	"@dyninst//:dyninst",
        "@glog//:glog",
    ],
    linkopts = ["-lrt"],
)

cc_binary(
    name = "stack_protector",
    srcs = [
	"parse.cc",
	"parse.h",
        "stack_protector.cc",
	"utils.cc",
	"utils.h",
    ],
    deps = [
        "@com_github_gflags_gflags//:gflags",
        "@glog//:glog",
       	"@dyninst//:dyninst",
    ],
)

cc_library(
    name = "stackrt",
    srcs = [
        "runtime.c",
    ],
    deps = [
        "@dyninst//:dyninst",
    ],
    visibility = ["//visibility:public"],
    linkopts = ["-ldl"],
)

cc_library(
    name = "analysis",
    srcs = [
	"heap.h",
        "passes.h",
        "pass_manager.h",
	"register_utils.h",
	"utils.cc",
	"utils.h",
    ],
    deps = [
        "@dyninst//:dyninst",
        "@com_github_gflags_gflags//:gflags",
        "@glog//:glog",
    ],
    visibility = ["//visibility:public"],
)

cc_binary(
    name = "symbolic_analysis",
    srcs = [
	"symbolic.cc",
    ],
    deps = [
	"//src:analysis",
        "@dyninst//:dyninst",
        "@com_github_gflags_gflags//:gflags",
        "@glog//:glog",
    ],
    visibility = ["//visibility:public"],
)

cc_binary(
    name = "test_app",
    srcs = [
	"test_app.cc",
    ],
    deps = [
    ],
    visibility = ["//visibility:public"],
)

cc_binary(
    name = "test",
    srcs = [
	"heap.h",
	"test.cc",
	"passes.h",
	"pass_manager.h",
	"utils.cc",
	"utils.h",
	"register_utils.h",
    ],
    deps = [
        "@dyninst//:dyninst",
        "@com_github_gflags_gflags//:gflags",
        "@glog//:glog",
    ],
    visibility = ["//visibility:public"],
)
