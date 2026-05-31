import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberTotalBoundedConsumerFactorization [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead streamRead
      regularRead realRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover window radius →
        Cont radius mesh dyadicRead →
          Cont dyadicRead route streamRead →
            Cont streamRead provenance regularRead →
              Cont regularRead nameRow realRead →
                Cont realRead transport compactRead →
                  PkgSig bundle compactRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                            hsame row mesh ∨ hsame row dyadicRead ∨ hsame row streamRead ∨
                              hsame row regularRead ∨ hsame row realRead ∨
                                hsame row compactRead)
                        (fun row : BHist =>
                          PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
                            hsame row compactRead)
                        hsame ∧
                      UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory realRead ∧
                          UnaryHistory compactRead ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier _coverWindowRadius radiusMeshDyadic dyadicRouteStream
  intro streamProvenanceRegular regularNameReal realTransportCompact compactPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _carrierCoverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary routeUnary dyadicRouteStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary provenanceUnary streamProvenanceRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed realUnary transportUnary realTransportCompact
  have sourceCompact :
      (fun row : BHist => hsame row compactRead ∧ UnaryHistory row) compactRead := by
    exact ⟨hsame_refl compactRead, compactUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨
              hsame row mesh ∨ hsame row dyadicRead ∨ hsame row streamRead ∨
                hsame row regularRead ∨ hsame row realRead ∨ hsame row compactRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
              hsame row compactRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro compactRead sourceCompact
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, compactPkg, source.left⟩
    }
  exact
    ⟨cert, dyadicUnary, streamUnary, regularUnary, realUnary, compactUnary, provenancePkg,
      compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
