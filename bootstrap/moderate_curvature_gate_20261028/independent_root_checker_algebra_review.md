# Algebra review of the independent Q42 bias checker

28 October2026. Reviewer: hcm_end_to_end. No rerun or source change.

**Verdict: no algebra or rounding-direction error found.** This review concerns the independently implemented checker, not an independent review of the proposition I authored.

Reviewed `root_check_bias.py`, SHA256 `b69bcda461616112b4147a205d8ec58056ab852ec6999613332086ffbf506dd1`, and its retained certificate bound to proposition SHA256 `863d6b4751e273442d32e65aa720ee90f79d0737f390b67d880dd030152af9b3`.

Write lo/Q<=eta_t<=hi/Q, d=Q-hi, c=2Q-lo. The checker stores lower v and mean bounds and upper u and w bounds, all at scale Q. Since every coefficient and state being multiplied is nonnegative:

- `h=max(0,(3*v-2*w)//6)` is a valid lower bound at scale Q for max(0,v_exact/2-w_exact/3).
- `(d*mean+lo*h)//Q` uses lower bounds for both nonnegative mean-recursion terms. Shared dependence of the two coefficients on eta does not invalidate these separate lower bounds.
- `(d*d*v+16*lo*lo*Q)//Q**2` is exactly the lower second-moment recursion with downward rounding.
- `up(c*c*u+64*hi*hi*Q,4*Q**2)` equals the upper recursion `(c/(2Q))^2*u+16*hi^2/Q`, rounded upward.
- The fourth-moment update has the common denominator16Q^4. Its three numerators are `c^4*w`, `384*hi^2*c^2*u`, and `4096*hi^4*Q`. They respectively represent `c_t^4*w`, `96*eta_t^2*c_t^2*u`, and the scale-Q value of `256*eta_t^4`. All constants and powers of Q are correct.

First-step moments use X1=eta1 Z1 exactly. All subsequent contractions are positive, as asserted. The gain endpoints are verified by integer100th-power inequalities; the floating-point value is only an initial guess. Fused one-sided polynomial rounding can give a slightly stronger lower bound than the producer's finer-scale interval implementation, so the ordering of the two retained results is not a contradiction.

The retained rational lower bound `23081750376873377/4398046511104000000` exceeds `131/25000`, as reported. The scope remains a certified negative mean; neither checker establishes the bootstrap coverage probability.
