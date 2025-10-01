// Lean compiler output
// Module: rh.Proof.Main
// Imports: Init rh.academic_framework.Certificate rh.RS.SchurGlobalization rh.RS.BoundaryWedgeProof rh.Cert.KxiWhitney Mathlib.Topology.Defs.Filter rh.academic_framework.EulerProductMathlib rh.academic_framework.CompletedXi rh.academic_framework.CompletedXiSymmetry rh.academic_framework.Theta rh.RS.OffZerosBridge rh.RS.Cayley rh.RS.PinchCertificate rh.RS.XiExtBridge rh.RS.SchurGlobalization rh.RS.CRGreenOuter Mathlib.NumberTheory.LSeries.RiemannZeta Mathlib.Tactic Mathlib.Analysis.SpecialFunctions.Gamma.Deligne Mathlib.Topology.Basic rh.RS.PinchIngredients
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
lean_object* initialize_rh_academic__framework_Certificate(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_SchurGlobalization(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_BoundaryWedgeProof(uint8_t builtin, lean_object*);
lean_object* initialize_rh_Cert_KxiWhitney(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Defs_Filter(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_EulerProductMathlib(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_CompletedXi(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_CompletedXiSymmetry(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_Theta(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_OffZerosBridge(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_Cayley(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_PinchCertificate(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_XiExtBridge(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_SchurGlobalization(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_CRGreenOuter(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Gamma_Deligne(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_PinchIngredients(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_Proof_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_Certificate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_SchurGlobalization(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_BoundaryWedgeProof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_Cert_KxiWhitney(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Defs_Filter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_EulerProductMathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_CompletedXi(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_CompletedXiSymmetry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_Theta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_OffZerosBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_Cayley(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_PinchCertificate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_XiExtBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_SchurGlobalization(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_CRGreenOuter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Gamma_Deligne(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_PinchIngredients(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
