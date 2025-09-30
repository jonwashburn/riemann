// Lean compiler output
// Module: rh.RS.CertificateConstruction
// Imports: Init rh.RS.CRGreenOuter rh.RS.BoundaryWedgeProof rh.RS.PinchCertificate rh.RS.Det2Outer rh.academic_framework.CompletedXi rh.Proof.Main
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
lean_object* initialize_rh_RS_BoundaryWedgeProof(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_PinchCertificate(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_Det2Outer(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_CompletedXi(uint8_t builtin, lean_object*);
lean_object* initialize_rh_Proof_Main(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_RS_CertificateConstruction(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_CRGreenOuter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_BoundaryWedgeProof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_PinchCertificate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_Det2Outer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_CompletedXi(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_Proof_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
