// Lean compiler output
// Module: rh.RS.BoundaryWedgeProof
// Imports: Init rh.RS.CRGreenOuter rh.RS.PoissonPlateauNew rh.RS.PoissonPlateauCore rh.Cert.KxiPPlus rh.academic_framework.HalfPlaneOuterV2 Mathlib.Tactic
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_CRGreenOuter(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_PoissonPlateauNew(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_PoissonPlateauCore(uint8_t builtin, lean_object*);
lean_object* initialize_rh_Cert_KxiPPlus(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_HalfPlaneOuterV2(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_RS_BoundaryWedgeProof(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_CRGreenOuter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_PoissonPlateauNew(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_PoissonPlateauCore(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_Cert_KxiPPlus(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_HalfPlaneOuterV2(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
