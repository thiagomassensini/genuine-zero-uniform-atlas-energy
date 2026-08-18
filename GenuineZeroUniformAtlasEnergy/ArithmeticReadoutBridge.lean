import GenuineZeroUniformAtlasEnergy.FinalConfinementProbe
import GenuineZeroUniformAtlasEnergy.EmpiricalTransverseDataCrosswalk
import NativeCarryC3Crosswalk.ArithmeticNonlocalTrace

/-!
# Canonical arithmetic nonlocal readout bridge

This module reuses the already kernel-checked arithmetic nonlocal trace from
`NativeCarryC3Crosswalk` instead of duplicating its construction here.

The readout is the maximal inverse of the bounded critical-amplitude damping
`p^(-1/2)`.  Its graph is a fixed closed maximal Green-isotropic boundary
relation.  The only spectral regularity question is whether the canonical mass
state attached to a Genuine zero belongs to that explicit proper dense domain.

The purpose of this bridge is to connect that operator-domain statement to the
scalar confinement endpoint in this repository with no numerical premise and
no redefinition of the zero predicate.
-/

namespace GenuineZeroUniformAtlasEnergy

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The imported arithmetic readout is a closed partial operator. -/
theorem arithmeticReadout_isClosed :
    arithmeticNonlocalTrace.IsClosed :=
  arithmeticNonlocalTrace_isClosed

/-- The imported arithmetic readout is self-adjoint on its maximal domain. -/
theorem arithmeticReadout_isSelfAdjoint :
    IsSelfAdjoint arithmeticNonlocalTrace :=
  arithmeticNonlocalTrace_isSelfAdjoint

/-- Its graph is a maximal Green-isotropic boundary relation. -/
theorem arithmeticReadout_boundaryRelation_isMaximalGreenIsotropic :
    IsMaximalGreenIsotropic arithmeticNonlocalBoundaryRelation :=
  arithmeticNonlocalBoundaryRelation_isMaximalGreenIsotropic

/-- Every canonical graph value belongs to the fixed arithmetic boundary
relation before any spectral-zero hypothesis is introduced. -/
theorem arithmeticReadout_boundaryPort_mem_relation
    (mass : arithmeticNonlocalTrace.domain) :
    arithmeticNonlocalBoundaryPort mass ∈
      arithmeticNonlocalBoundaryRelation :=
  arithmeticNonlocalBoundaryPort_mem_relation mass

/-- The exact logical crosswalk between the scalar endpoint of this repository
and the domain regularity of the canonical arithmetic readout. -/
theorem finalGenuineZeroConfinement_iff_arithmeticReadoutDomain :
    FinalGenuineZeroConfinement ↔
      GenuineZerosLieInArithmeticNonlocalTraceDomain := by
  exact finalGenuineZeroConfinement_iff_strongNonvanishing.trans
    genuineZero_to_arithmeticNonlocalTrace_domain_iff_strongNonvanishing.symm

/-- Therefore a proof that Genuine zeros lie in the canonical arithmetic
readout domain closes the scalar confinement theorem immediately. -/
theorem finalGenuineZeroConfinement_of_arithmeticReadoutDomain
    (hreadout : GenuineZerosLieInArithmeticNonlocalTraceDomain) :
    FinalGenuineZeroConfinement :=
  finalGenuineZeroConfinement_iff_arithmeticReadoutDomain.mpr hreadout

end

end GenuineZeroUniformAtlasEnergy
