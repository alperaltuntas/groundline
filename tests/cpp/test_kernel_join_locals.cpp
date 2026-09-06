// Conformance fixture (C++ side): the flux_elem_point construct set — the
// mirror of tests/f90/test_kernel_join_locals. (1) a `bool const` parameter
// used as a bare `if` condition (a Bool input); (2) locals DECLARED WITHOUT AN
// INITIALIZER and assigned later, inside the branches of an if / else if /
// else that statements follow — the generalized control-flow join, with a
// nested join inside each branch; (3) the refuse_* siblings pin the
// neighboring shapes. The prelude mirrors amrex::Real / amrex::literals so the
// fixture is self-contained (no includes; clang++ alone suffices).

using Real = double;
constexpr Real operator""_rt(long double v) { return static_cast<Real>(v); }

// Supported: the distilled flux_elem_point shape (same argument order as the
// Fortran twin, minus its unreferenced grid dummy).
void face_flux_point(Real const u, Real const h, Real const h_p1, Real& q, Real& dq,
                     Real const dt, bool const vol_cfl, Real const area) noexcept
{
    Real const tmp = area * dt;
    Real cfl, w;
    if (u > 0.0_rt) {
        if (vol_cfl) { cfl = u * dt; } else { cfl = u * area; }
        w = h * (1.0_rt - cfl);
        q = tmp * u * w;
    } else if (u < 0.0_rt) {
        if (vol_cfl) { cfl = u * dt; } else { cfl = u * area; }
        w = h_p1 * (1.0_rt - cfl);
        q = tmp * u * w;
    } else {
        q = 0.0_rt;
        w = 0.5_rt * (h + h_p1);
    }
    dq = tmp * w;
}

// REFUSAL (functionalize): `w` is assigned on the then-path only, never
// initialized before the if, and read after the join.
void refuse_partial_local(Real const u, Real& q) noexcept
{
    Real w;
    if (u > 0.0_rt) { w = u; }
    q = q + w;
}

// Supported neighbor: the same shape, but `w` is initialized before the if.
void rebound_local_point(Real const u, Real& q) noexcept
{
    Real w = 1.0_rt;
    if (u > 0.0_rt) { w = u; }
    q = q + w;
}

// Supported (2026-09-05): a bool local — a `let` of a Bool-valued expression
// (here a comparison, in column kernels a flag read), used as an `if` guard.
void bool_local_point(Real const u, Real& q) noexcept
{
    bool const pos = u > 0.0_rt;
    if (pos) { q = q + u; }
}

// REFUSAL (functionalize): a local read before any assignment.
void refuse_read_unset(Real const u, Real& q) noexcept
{
    Real w;
    q = q + w;
    w = u;
}

// REFUSAL: a list-initialized local — only `= e` initializers and bare
// declarations are admitted.
void refuse_list_init(Real const u, Real& q) noexcept
{
    Real w{u};
    q = q + w;
}
