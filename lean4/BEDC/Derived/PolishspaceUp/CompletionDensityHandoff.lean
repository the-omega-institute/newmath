import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PolishSpaceCarrier [AskSetup] [PackageSetup]
    (M K D S R W H C G N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory M ∧ UnaryHistory K ∧ UnaryHistory D ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory G ∧ UnaryHistory N ∧ Cont M K W ∧ Cont W S R ∧
        Cont H C G ∧ PkgSig bundle G pkg

theorem PolishSpaceCarrier_completion_density_handoff [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead densityRead commonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont M K completionRead ->
        Cont M D densityRead ->
          Cont completionRead densityRead commonRead ->
            PkgSig bundle commonRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  (hsame row completionRead ∨ hsame row densityRead ∨ hsame row commonRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row W ∨
                    hsame row completionRead ∨ hsame row densityRead ∨ hsame row commonRead)
                (fun _row : BHist => PkgSig bundle G pkg ∧ PkgSig bundle commonRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier completionRoute densityRoute commonRoute commonPkg
  obtain ⟨MUnary, KUnary, DUnary, _SUnary, _RUnary, _WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, carrierPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed MUnary DUnary densityRoute
  have commonUnary : UnaryHistory commonRead :=
    unary_cont_closed completionUnary densityUnary commonRoute
  have sourceCommon :
      (fun row : BHist =>
        (hsame row completionRead ∨ hsame row densityRead ∨ hsame row commonRead) ∧
          UnaryHistory row) commonRead := by
    exact ⟨Or.inr (Or.inr (hsame_refl commonRead)), commonUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro commonRead sourceCommon
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
        have sourceRoute :
            hsame _other completionRead ∨ hsame _other densityRead ∨
              hsame _other commonRead := by
          cases source.left with
          | inl completionSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) completionSame)
          | inr tail =>
              cases tail with
              | inl densitySame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) densitySame))
              | inr commonSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) commonSame))
        exact ⟨sourceRoute, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl completionSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl completionSame))))
      | inr tail =>
          cases tail with
          | inl densitySame =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl densitySame)))))
          | inr commonSame =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr commonSame)))))
    ledger_sound := by
      intro _row _source
      exact ⟨carrierPkg, commonPkg⟩
  }

end BEDC.Derived.PolishSpaceUp
