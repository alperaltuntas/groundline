// Conformance fixture (C++ side): `amrex::max` / `amrex::min` callees, and
// the JSON shapes their const-reference signature drags in — the mirror of
// tests/f90/test_kernel_stencil's `max(...)`. The prelude mirrors AMReX's
// templates (`const T& max(const T&, const T&)`), so a call produces exactly
// the production AST: `ExprWithCleanups` around the return value,
// `MaterializeTemporaryExpr` + a `NoOp` cast binding a prvalue argument to
// the const reference, and an `LValueToRValue` cast reading the returned
// reference. A three-argument `max` and a `pow` call pin the callee gate.

using Real = double;
constexpr Real operator""_rt(long double v) { return static_cast<Real>(v); }
namespace amrex {
template <class T> constexpr const T& max(const T& a, const T& b) noexcept { return (b > a) ? b : a; }
template <class T> constexpr const T& min(const T& a, const T& b) noexcept { return (b < a) ? b : a; }
template <class T> constexpr const T& max(const T& a, const T& b, const T& c) noexcept { return max(max(a, b), c); }
}
Real pow(Real, Real);

// Supported: the distilled continuity_convergence_point.
Real converge_point(Real const h_prev, Real const flux_out, Real const flux_in,
                    Real const dt, Real const iarea, Real const h_min) noexcept
{
    return amrex::max(h_prev - dt * iarea * (flux_out - flux_in), h_min);
}

// Supported: nested min/max in a void kernel (the inner call's returned
// reference is passed straight through, no temporary).
void clamp_point(Real& x, Real const lo, Real const hi) noexcept
{
    x = amrex::min(amrex::max(x, lo), hi);
}

// REFUSAL: AMReX's three-argument max — only the binary form is modeled.
Real refuse_max_three(Real const a, Real const b, Real const c) noexcept
{
    return amrex::max(a, b, c);
}

// REFUSAL: a callee outside the intrinsic set.
Real refuse_pow(Real const a) noexcept
{
    return pow(a, 2.0_rt);
}
