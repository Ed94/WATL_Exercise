/*
WATL Exercise
Version: 2 (From Scratch, 2-Stage Compilation)

Vendor OS & Compiler: Windows 11, MSVC
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
