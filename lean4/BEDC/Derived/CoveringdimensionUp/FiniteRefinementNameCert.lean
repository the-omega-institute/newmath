import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionFiniteRefinementCarrier [AskSetup] [PackageSetup]
    (K E C R O L S M A G H T P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  UnaryHistory K ∧ UnaryHistory E ∧ UnaryHistory C ∧ UnaryHistory R ∧
    UnaryHistory O ∧ UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory M ∧
      UnaryHistory A ∧ UnaryHistory G ∧ UnaryHistory H ∧ UnaryHistory T ∧
        UnaryHistory P ∧ UnaryHistory N ∧ Cont K E C ∧ Cont C R O ∧
          Cont O L T ∧ Cont S M A ∧ Cont A G H ∧ Cont H T P ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CoveringDimensionFiniteRefinementNameCertObligations [AskSetup] [PackageSetup]
    {K E C R O L S M A G H T P N orderRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteRefinementCarrier K E C R O L S M A G H T P N bundle pkg →
      Cont O L orderRead →
        Cont orderRead T namedRead →
          PkgSig bundle namedRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row orderRead ∨ hsame row namedRead ∨ hsame row N)
                (fun row : BHist => UnaryHistory row)
                (fun _row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                hsame ∧
              UnaryHistory orderRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier orderRoute namedRoute namedPkg
  obtain ⟨_KUnary, _EUnary, _CUnary, _RUnary, OUnary, LUnary, _SUnary, _MUnary,
    _AUnary, _GUnary, _HUnary, TUnary, _PUnary, NUnary, _KELedger, _CROrder,
    _OLTReplay, _SMAWindow, _AGTransport, _HTProvenance, provenancePkg, _namePkg⟩ :=
      carrier
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed OUnary LUnary orderRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed orderReadUnary TUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderRead ∨ hsame row namedRead ∨ hsame row N)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro orderRead (Or.inl (hsame_refl orderRead))
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
        cases source with
        | inl orderSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) orderSource)
        | inr rest =>
            cases rest with
            | inl namedSource =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) namedSource))
            | inr nameSource =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) nameSource))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl orderSource =>
          exact unary_transport orderReadUnary (hsame_symm orderSource)
      | inr rest =>
          cases rest with
          | inl namedSource =>
              exact unary_transport namedReadUnary (hsame_symm namedSource)
          | inr nameSource =>
              exact unary_transport NUnary (hsame_symm nameSource)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, namedPkg⟩
  }
  exact ⟨cert, orderReadUnary, namedReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
