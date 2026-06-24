import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationSeparatedRefinementExactness [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverWindow restrictionRead separatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T coverWindow →
        Cont J P restrictionRead →
          Cont coverWindow restrictionRead separatedRead →
            PkgSig bundle separatedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                      hsame row L ∨ hsame row coverWindow ∨ hsame row restrictionRead ∨
                        hsame row separatedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont C T coverWindow ∧ Cont J P restrictionRead ∧
                      Cont coverWindow restrictionRead separatedRead ∧
                        PkgSig bundle separatedRead pkg)
                  hsame ∧
                UnaryHistory coverWindow ∧ UnaryHistory restrictionRead ∧
                  UnaryHistory separatedRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier coverRoute restrictionRoute separatedRoute separatedPkg
  obtain ⟨CUnary, TUnary, JUnary, PUnary, _LUnary, _GUnary, _SUnary, _HUnary, _RUnary,
    _QUnary, _NUnary, namePkg⟩ := carrier
  have coverWindowUnary : UnaryHistory coverWindow :=
    unary_cont_closed CUnary TUnary coverRoute
  have restrictionReadUnary : UnaryHistory restrictionRead :=
    unary_cont_closed JUnary PUnary restrictionRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed coverWindowUnary restrictionReadUnary separatedRoute
  have sourceSeparated : hsame separatedRead separatedRead ∧ UnaryHistory separatedRead :=
    ⟨hsame_refl separatedRead, separatedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
              hsame row L ∨ hsame row coverWindow ∨ hsame row restrictionRead ∨
                hsame row separatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C T coverWindow ∧ Cont J P restrictionRead ∧
              Cont coverWindow restrictionRead separatedRead ∧ PkgSig bundle separatedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro separatedRead sourceSeparated
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coverRoute, restrictionRoute, separatedRoute, separatedPkg⟩
  }
  exact ⟨cert, coverWindowUnary, restrictionReadUnary, separatedReadUnary, namePkg⟩

end BEDC.Derived.SheafificationUp
