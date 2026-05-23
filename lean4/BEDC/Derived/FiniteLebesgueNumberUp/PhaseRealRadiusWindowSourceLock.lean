import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPhaseRealRadiusWindowSourceLock [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead streamRead sealRead
      sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius mesh dyadicRead →
        Cont dyadicRead window streamRead →
          Cont streamRead route sealRead →
            Cont sealRead nameRow sourceRead →
              PkgSig bundle sourceRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row dyadicRead ∨ hsame row streamRead ∨
                        hsame row sealRead ∨ hsame row sourceRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle sourceRead pkg ∧
                        hsame row sourceRead)
                    hsame ∧
                  UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory sourceRead ∧
                      Cont radius mesh dyadicRead ∧ Cont dyadicRead window streamRead ∧
                        Cont streamRead route sealRead ∧
                          Cont sealRead nameRow sourceRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier radiusMeshDyadic dyadicWindowStream streamRouteSeal sealNameSource
    sourcePkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed streamUnary routeUnary streamRouteSeal
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sealUnary nameRowUnary sealNameSource
  have sourceCarrier :
      (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row) sourceRead := by
    exact ⟨hsame_refl sourceRead, sourceUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row sealRead ∨
            hsame row sourceRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle sourceRead pkg ∧
            hsame row sourceRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sourceRead sourceCarrier
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, sourcePkg, source.left⟩
    }
  exact
    ⟨cert, dyadicUnary, streamUnary, sealUnary, sourceUnary, radiusMeshDyadic,
      dyadicWindowStream, streamRouteSeal, sealNameSource, provenancePkg, sourcePkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
