$misc = Join-Path $PSScriptRoot 'helpers/misc.psm1'
import-module $misc

# This script now uses the LLVM toolchain (clang-cl, lld-link).
# Ensure these tools are available in your PATH.
# The original call to the MSVC devshell has been removed.
# & (join-path $PSScriptRoot 'helpers/devshell.ps1') -arch amd64

$path_root = Get-ScriptRepoRoot

$path_root      = split-path -Path $PSScriptRoot -Parent
$path_toolchain = join-path $path_root      'toolchain'
$path_rad       = join-path $path_toolchain 'rad'

# https://learn.microsoft.com/en-us/cpp/build/reference/compiler-options-listed-by-category?view=msvc-170
# Most cl.exe flags are compatible with clang-cl.exe
$flag_all_c                        = '/TC'
$flag_c11                          = '/std:c11'
$flag_c23                          = '/std:c23'
$flag_all_cpp                      = '/TP'
$flag_compile                      = '/c'
$flag_charset_utf8                 = '/utf-8'
$flag_debug                        = '/Zi'
$flag_define                       = '/D'
$flag_exceptions_disabled          = '/EHsc-'
$flag_RTTI_disabled                = '/GR-'
$flag_include                      = '/I'
$flag_full_src_path                = '/FC'
$flag_asm_listing_file             = '/FAs'
$flag_nologo                       = '/nologo'
$flag_dll                          = '/LD'
$flag_dll_debug                    = '/LDd'
$flag_linker                       = '/link'
# $flag_link_lib                     = '/lib'
$flag_link_dll                     = '/DLL'
$flag_link_no_incremental          = '/INCREMENTAL:NO'
$flag_link_mapfile                 = '/MAP:'
$flag_link_optimize_references     = '/OPT:REF'
$flag_link_win_debug               = '/DEBUG'
$flag_link_win_pdb                 = '/PDB:'
$flag_link_win_machine_32          = '/MACHINE:X86'
$flag_link_win_machine_64          = '/MACHINE:X64'
$flag_link_win_path_output         = '/OUT:'
$flag_link_win_rt_dll              = '/MD'
$flag_link_win_rt_dll_debug        = '/MDd'
$flag_link_win_rt_static           = '/MT'
$flag_link_win_rt_static_debug     = '/MTd'
$flag_link_win_subsystem_console   = '/SUBSYSTEM:CONSOLE'
$flag_link_win_subsystem_windows   = '/SUBSYSTEM:WINDOWS'
$flag_no_optimization              = '/Od'
$flag_optimize_speed_max           = '/Ox'
$flag_optimize_fast                = '/O2'
$flag_optimize_size                = '/O1'
$flag_optimize_intrinsics          = '/Oi'
$flag_optimized_debug_forceinline  = '/d2Obforceinline'
$flag_optimized_debug              = '/Zo'
$flag_preprocess_to_file           = '/P'
$flag_preprocess_preserve_comments = '/C'
# $flag_out_name                     = '/OUT:'
$flag_path_interm                  = '/Fo'
$flag_path_debug                   = '/Fd'
$flag_path_output                  = '/Fe'
$flag_preprocess_conform           = '/Zc:preprocessor'
$flag_sanitize_address             = '/fsanitize=address'
$flag_updated_cpp_macro            = "/Zc:__cplusplus"
$flag_set_stack_size               = '/F'
$flag_syntax_only                  = '/Zs'
$flag_wall                         = '/Wall'
$flag_warnings_as_errors           = '/WX'
$flag_lib_list                     = '/LIST'
 
$archiver = 'llvm-lib'
$compiler = 'clang-cl'
$linker   = 'lld-link'
$radbin   = join-path $path_rad 'radbin.exe'
$radlink  = join-path $path_rad 'radlink.exe'

$path_build = join-path $path_root 'build'
if ( -not(test-path -Path $path_build) ) {
	new-item -ItemType Directory -Path $path_build
}

push-location $path_build

write-host "Compiling with clang-cl"

$compiler_args = @()
$compiler_args += $flag_nologo

# Constraints on interpeting all files as C code
$compiler_args += $flag_all_c
$compiler_args += $flag_c11
# Constraints on C program code-gen 
$compiler_args += $flag_exceptions_disabled
$compiler_args += $flag_RTTI_disabled
# $compiler_args += $flag_preprocess_conform
# $compiler_args += $flag_sanitize_address

$compiler_args += $flag_wall

# Set charset encoding for both execution and source to UTF-8
$compiler_args += $flag_charset_utf8

# Specifing output pathing
$compiler_args += ( $flag_path_interm + $path_build + '\' )
# $compiler_args += ( $flag_path_output + $path_build + '\' )

# Dump preprocess file
if ($false) {
	$compiler_args += $flag_preprocess_to_file
	$compiler_args += $flag_preprocess_preserve_comments
}

# Diagnostic logging
$compiler_args += $flag_full_src_path
# $compiler_args += $flag_asm_listing_file

# $compiler_args += $flag_optimize_speed_max
# $compiler_args += $flag_optimize_fast
# $compiler_args += $flag_optimize_size
# $compiler_args += $flag_optimize_intrinsics
$compiler_args += $flag_no_optimization

# Debug setup
$compiler_args += ($flag_define + 'BUILD_DEBUG')
$compiler_args += $flag_debug
$compiler_args += ( $flag_path_debug + $path_build + '\' )
# Use the static, multithreaded, debug runtime library
# $compiler_args += $flag_link_win_rt_static_debug

# Include setup
$compiler_args += ($flag_include + $path_root)

$unit_name   = "watl.v0.llvm.lottes_hybrid"

# Specify unit to compile
$unit           = join-path $path_root "C\$unit_name.c"
$compiler_args += $flag_compile, $unit

# Diagnoistc print for the args
$compiler_args | ForEach-Object { Write-Host $_ }

# Compile the unit
$compilation_time = Measure-Command { 
	& $compiler $compiler_args 
}
write-host "Compilation took $($compilation_time.TotalMilliseconds)ms"
write-host

$binary = join-path $path_build "$unit_name.exe"
$object = join-path $path_build "$unit_name.obj"

$pdb         = join-path $path_build "$unit_name.pdb"
$map         = join-path $path_build "$unit_name.map"
$rdi         = join-path $path_build "$unit_name.rdi"
$rdi_listing = join-path $path_build "$unit_name.rdi.list"

if ($true) {
	write-host "Linking with lld-link"

	$linker_args = @()
	$linker_args += $flag_nologo
	$linker_args += $flag_link_win_machine_64
	$linker_args += $flag_link_no_incremental
	$linker_args += ($flag_link_win_path_output + $binary)

	$linker_args += "$flag_link_win_debug"
	$linker_args += $flag_link_win_pdb + $pdb
	$linker_args += $flag_link_mapfile + $map
    $linker_args += $flag_link_win_subsystem_console

	$linker_args += $object
    
    # Add necessary libraries for a basic Windows application
    $linker_args += "kernel32.lib", "user32.lib", "gdi32.lib"

	# Diagnoistc print for the args
	$linker_args | ForEach-Object { Write-Host $_ }

	$linking_time = Measure-Command { & $linker $linker_args }
	# & $radlink $linker_args
	write-host "Linking took $($linking_time.TotalMilliseconds)ms"
	write-host
}

if ($false) {
	write-host "Dumping Debug Info"

	$rbin_out  = '--out:'
	$rbin_dump = '--dump'

	$nargs = @($pdb, ($rbin_out + $rdi))
	& $radbin $nargs

	$nargs = @($rbin_dump, $rdi)
	$dump = & $radbin $nargs
	$dump > $rdi_listing
}

Pop-Location
