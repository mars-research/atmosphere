{ writeShellScriptBin, verus-unwrapped, rustc }:

writeShellScriptBin "rust_verify" ''
  exec ${verus-unwrapped}/bin/rust_verify \
    --pervasive-path ${verus-unwrapped.src}/source/pervasive \
    --extern builtin=${verus-unwrapped}/lib/libbuiltin.rlib \
    --extern builtin_macros=${verus-unwrapped}/lib/libbuiltin_macros.so \
    --extern state_machines_macros=${verus-unwrapped}/lib/libstate_machines_macros.so \
    --sysroot ${rustc} \
    "$@"
''
