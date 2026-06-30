import BEDC.Derived.CanonicalTailChoiceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_window_stability
    {M E I T S R H C0 P N tail tail' : BHist}
    (mUnary : UnaryHistory M)
    (eUnary : UnaryHistory E)
    (tUnary : UnaryHistory T)
    (indexRoute : Cont M E I)
    (tailRoute : Cont I T tail)
    (sameTail : hsame tail' tail) :
    UnaryHistory I ∧ UnaryHistory tail ∧ UnaryHistory tail' ∧
      Cont M E I ∧ Cont I T tail := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  have indexUnary : UnaryHistory I :=
    unary_cont_closed mUnary eUnary indexRoute
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed indexUnary tUnary tailRoute
  have tailPrimeUnary : UnaryHistory tail' :=
    unary_transport tailUnary (hsame_symm sameTail)
  have _sealRow : hsame S S := hsame_refl S
  have _refusalRow : hsame R R := hsame_refl R
  have _transportRow : hsame H H := hsame_refl H
  have _replayRow : hsame C0 C0 := hsame_refl C0
  have _provenanceRow : hsame P P := hsame_refl P
  have _nameRow : hsame N N := hsame_refl N
  exact ⟨indexUnary, tailUnary, tailPrimeUnary, indexRoute, tailRoute⟩

theorem CanonicalTailChoiceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory E →
        UnaryHistory I →
          UnaryHistory T →
            UnaryHistory S →
              UnaryHistory R →
                UnaryHistory H →
                  UnaryHistory C0 →
                    UnaryHistory P →
                      UnaryHistory N →
                        PkgSig bundle N pkg →
                          SemanticNameCert
                            (fun row : BHist => hsame row N ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row M ∨ hsame row E ∨ hsame row I ∨
                                hsame row T ∨ hsame row S ∨ hsame row R ∨
                                  hsame row H ∨ hsame row C0 ∨ hsame row P ∨
                                    hsame row N)
                            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _mUnary _eUnary _iUnary _tUnary _sUnary _rUnary _hUnary _c0Unary _pUnary
    nUnary nPkg
  refine
    { core :=
        { carrier_inhabited := ⟨N, hsame_refl N, nUnary⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows sourceRow
    exact
      ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
        unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr sourceRow.left))))))))
  · intro _row sourceRow
    exact ⟨sourceRow.right, nPkg⟩

end BEDC.Derived.CanonicalTailChoiceUp
