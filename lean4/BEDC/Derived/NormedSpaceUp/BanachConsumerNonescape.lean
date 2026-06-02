import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedSpaceCarrier_banach_consumer_nonescape [AskSetup] [PackageSetup]
    {V R N M Q H T P C completionRead banachRead hilbertRead operatorRead
      exportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg →
      Cont M Q completionRead →
        Cont completionRead H banachRead →
          Cont completionRead T hilbertRead →
            Cont completionRead C operatorRead →
              Cont banachRead operatorRead exportedRead →
                PkgSig bundle exportedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                          hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row C ∨
                            hsame row completionRead ∨ hsame row exportedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M Q completionRead ∧
                          PkgSig bundle exportedRead pkg)
                      hsame ∧
                    UnaryHistory completionRead ∧ UnaryHistory banachRead ∧
                      UnaryHistory hilbertRead ∧ UnaryHistory operatorRead ∧
                        UnaryHistory exportedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier completionRoute banachRoute hilbertRoute operatorRoute exportRoute exportedPkg
  obtain ⟨_vUnary, _rUnary, _nUnary, mUnary, qUnary, hUnary, tUnary, _pUnary,
    cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, _provenancePkg,
    _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary qUnary completionRoute
  have banachUnary : UnaryHistory banachRead :=
    unary_cont_closed completionUnary hUnary banachRoute
  have hilbertUnary : UnaryHistory hilbertRead :=
    unary_cont_closed completionUnary tUnary hilbertRoute
  have operatorUnary : UnaryHistory operatorRead :=
    unary_cont_closed completionUnary cUnary operatorRoute
  have exportedUnary : UnaryHistory exportedRead :=
    unary_cont_closed banachUnary operatorUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row C ∨
                hsame row completionRead ∨ hsame row exportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q completionRead ∧ PkgSig bundle exportedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportedRead ⟨hsame_refl exportedRead, exportedUnary⟩
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
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionRoute, exportedPkg⟩
  }
  exact
    ⟨cert, completionUnary, banachUnary, hilbertUnary, operatorUnary, exportedUnary⟩

end BEDC.Derived.NormedSpaceUp
