/-
Alternate A.1 route (stub): kept as a no-op module to avoid pulling heavy
measure-theoretic dependencies into the default build. The working route
does not import this file; users can replace it with a complete proof
without affecting current call sites.
-/

namespace RH
namespace RS

/-- Optional A.1 stub to keep the module non-empty and compilable. -/
theorem A1_optional_stub : True := trivial

end RS
end RH
