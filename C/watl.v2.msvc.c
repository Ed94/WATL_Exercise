/*
WATL Exercise
Version:   2 (From Scratch, 2-Stage Compilation, MSVC & WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: MSVC 19.43, C-Stanard: 11
*/

#if GEN_TIME == 1
#include "gencpp_c11.h"

int gen_main()
{

}
//#if GEN_TIME == 1
#endif

#if GEN_TIME == 0
#pragma region Header
#pragma endregion Header

#pragma region Implementation
#pragma endregion Implementation

int main()
{

}
//#if defined(GEN_TIME) == 0
#endif 
