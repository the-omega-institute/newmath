import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationCarrier_separated_refinement_transport [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N separatedRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L separatedRead →
        hsame separatedRead transportedRead →
          UnaryHistory separatedRead ∧ UnaryHistory transportedRead ∧
            Cont P L separatedRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier separatedRoute sameTransport
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, _gUnary, _sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, namePkg⟩ := carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed pUnary lUnary separatedRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_transport separatedUnary sameTransport
  exact ⟨separatedUnary, transportedUnary, separatedRoute, namePkg⟩

theorem SheafificationSeparatedRefinementTransport [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverWindow restrictionRead separatedRead transportedRead
      sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T coverWindow →
        Cont J P restrictionRead →
          Cont coverWindow restrictionRead separatedRead →
            hsame transportedRead separatedRead →
              Cont transportedRead S sheafRead →
                PkgSig bundle Q pkg →
                  PkgSig bundle N pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                            hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                              hsame row R ∨ hsame row Q ∨ hsame row N ∨
                                hsame row separatedRead ∨ hsame row transportedRead ∨
                                  hsame row sheafRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont C T coverWindow ∧
                            Cont J P restrictionRead ∧
                              Cont coverWindow restrictionRead separatedRead ∧
                                Cont transportedRead S sheafRead ∧ PkgSig bundle Q pkg ∧
                                  PkgSig bundle N pkg)
                        hsame ∧ UnaryHistory separatedRead ∧
                      UnaryHistory transportedRead ∧ UnaryHistory sheafRead := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier coverRoute restrictionRoute separatedRoute sameTransport sheafRoute qPkg nPkg
  obtain ⟨cUnary, tUnary, jUnary, pUnary, _lUnary, _gUnary, sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qCarrierPkg, _nCarrierPkg⟩ := carrier
  have coverWindowUnary : UnaryHistory coverWindow :=
    unary_cont_closed cUnary tUnary coverRoute
  have restrictionReadUnary : UnaryHistory restrictionRead :=
    unary_cont_closed jUnary pUnary restrictionRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed coverWindowUnary restrictionReadUnary separatedRoute
  have transportedReadUnary : UnaryHistory transportedRead :=
    unary_transport separatedReadUnary (hsame_symm sameTransport)
  have sheafReadUnary : UnaryHistory sheafRead :=
    unary_cont_closed transportedReadUnary sUnary sheafRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
              hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                hsame row R ∨ hsame row Q ∨ hsame row N ∨
                  hsame row separatedRead ∨ hsame row transportedRead ∨ hsame row sheafRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C T coverWindow ∧ Cont J P restrictionRead ∧
              Cont coverWindow restrictionRead separatedRead ∧
                Cont transportedRead S sheafRead ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sheafRead ⟨hsame_refl sheafRead, sheafReadUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRoute, restrictionRoute, separatedRoute, sheafRoute, qPkg, nPkg⟩
  }
  exact ⟨cert, separatedReadUnary, transportedReadUnary, sheafReadUnary⟩

end BEDC.Derived.SheafificationUp
