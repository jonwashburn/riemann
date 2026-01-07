import Mathlib
import Mathlib.Analysis.InnerProductSpace.Harmonic.Poisson
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.HarmonicBounds
import Riemann.Mathlib.Analysis.Complex.HardySpace.PoissonKernel

-- quick name discovery for harmonic/Poisson APIs available in this snapshot

#check InnerProductSpace.HarmonicOnNhd
#check HarmonicOnNhd.circleAverage_eq

#print prefix HarmonicOnNhd

#print prefix InnerProductSpace.HarmonicOnNhd

-- check whether Mathlib has a Poisson kernel / Poisson integral for balls (inner product spaces)
#check ValueDistribution.log_norm_le_characteristic

-- Cauchy circle integral formulas (used to derive Poisson estimates in ℂ)
#check Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable

-- Try to locate any built-in Harnack/Poisson inequalities for harmonic functions
#check HarmonicOnNhd.harnack
#check HarmonicOnNhd.harnack_inequality
#check InnerProductSpace.HarmonicOnNhd.harnack
