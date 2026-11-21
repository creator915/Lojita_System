module N10_AutoImplicitTypo where
-- Default Lean 4 (`autoImplicit = true`) silently accepts `Nta → Nta`!
typo : Nta → Nta
typo x = x
