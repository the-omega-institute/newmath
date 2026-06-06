import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactBaireRealWindowAdmission [AskSetup] [PackageSetup]
    {K B S W R E H C P N baireRead windowRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont K B baireRead →
        Cont baireRead W windowRead →
          Cont windowRead R regularRead →
            Cont regularRead E realRead →
              PkgSig bundle realRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row realRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                        hsame row E ∨ hsame row baireRead ∨ hsame row windowRead ∨
                          hsame row regularRead ∨ hsame row realRead)
                    (fun row : BHist =>
                      hsame row realRead ∧ Cont K B baireRead ∧
                        Cont baireRead W windowRead ∧ Cont windowRead R regularRead ∧
                          Cont regularRead E realRead ∧ PkgSig bundle realRead pkg)
                    hsame ∧ UnaryHistory baireRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory regularRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier baireRoute windowRoute regularRoute realRoute realPkg
  obtain ⟨kUnary, bUnary, _sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular,
    _regularSealTransport, _transportReplayProvenance, _provenancePkg⟩ := carrier
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed kUnary bUnary baireRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed baireUnary wUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary eUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row realRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row baireRead ∨ hsame row windowRead ∨ hsame row regularRead ∨
                hsame row realRead)
          (fun row : BHist =>
            hsame row realRead ∧ Cont K B baireRead ∧ Cont baireRead W windowRead ∧
              Cont windowRead R regularRead ∧ Cont regularRead E realRead ∧
                PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead
        ⟨hsame_refl realRead, realUnary, realPkg⟩
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, baireRoute, windowRoute, regularRoute, realRoute, realPkg⟩
  }
  exact ⟨cert, baireUnary, windowUnary, regularUnary, realUnary⟩

end BEDC.Derived.SequentialCompactUp
