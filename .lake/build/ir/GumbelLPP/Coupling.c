// Lean compiler output
// Module: GumbelLPP.Coupling
// Imports: public import Init public import GumbelLPP.Imports public import GumbelLPP.GumbelFunction public import GumbelLPP.GridPaths
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* lp_GumbelLPP_F__GUE___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GumbelLPP_sigma__g;
LEAN_EXPORT lean_object* lp_GumbelLPP_C__g;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* lp_GumbelLPP_F__GUE(lean_object*);
static lean_object* _init_lp_GumbelLPP_C__g() {
_start:
{
lean_object* x_1; 
x_1 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
return x_1;
}
}
static lean_object* _init_lp_GumbelLPP_sigma__g() {
_start:
{
lean_object* x_1; 
x_1 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_GumbelLPP_F__GUE(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
return x_2;
}
}
LEAN_EXPORT lean_object* lp_GumbelLPP_F__GUE___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_GumbelLPP_F__GUE(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GumbelLPP_GumbelLPP_Imports(uint8_t builtin);
lean_object* initialize_GumbelLPP_GumbelLPP_GumbelFunction(uint8_t builtin);
lean_object* initialize_GumbelLPP_GumbelLPP_GridPaths(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GumbelLPP_GumbelLPP_Coupling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GumbelLPP_GumbelLPP_Imports(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GumbelLPP_GumbelLPP_GumbelFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GumbelLPP_GumbelLPP_GridPaths(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GumbelLPP_C__g = _init_lp_GumbelLPP_C__g();
lean_mark_persistent(lp_GumbelLPP_C__g);
lp_GumbelLPP_sigma__g = _init_lp_GumbelLPP_sigma__g();
lean_mark_persistent(lp_GumbelLPP_sigma__g);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
