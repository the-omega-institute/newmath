import BEDC.Derived.MooreOsgoodUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MooreOsgoodUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MooreOsgoodCarrier [AskSetup] [PackageSetup]
    (W F S U Q R D E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory W ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory Q ∧
    UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem MooreOsgoodIteratedLimitHandoff [AskSetup] [PackageSetup]
    {W F S U Q R D E H C P N firstRead secondRead uniformRead scheduleRead regularRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreOsgoodCarrier W F S U Q R D E H C P N bundle pkg →
      Cont W F firstRead →
        Cont W S secondRead →
          Cont U Q uniformRead →
            Cont uniformRead R regularRead →
              Cont regularRead E sealRead →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row W ∨ hsame row F ∨ hsame row S ∨ hsame row U ∨
                          hsame row Q ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                            hsame row firstRead ∨ hsame row secondRead ∨
                              hsame row uniformRead ∨ hsame row regularRead ∨
                                hsame row sealRead)
                      (fun row : BHist =>
                        hsame row sealRead ∧ Cont W F firstRead ∧ Cont W S secondRead ∧
                          Cont U Q uniformRead ∧ Cont uniformRead R regularRead ∧
                            Cont regularRead E sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle sealRead pkg)
                      hsame ∧ UnaryHistory firstRead ∧ UnaryHistory secondRead ∧
                    UnaryHistory uniformRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier firstRoute secondRoute uniformRoute regularRoute sealRoute sealPkg
  obtain ⟨wUnary, fUnary, sUnary, uUnary, qUnary, rUnary, _dUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, provenancePkg, _namePkg⟩ := carrier
  have firstUnary : UnaryHistory firstRead :=
    unary_cont_closed wUnary fUnary firstRoute
  have secondUnary : UnaryHistory secondRead :=
    unary_cont_closed wUnary sUnary secondRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed uUnary qUnary uniformRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed uniformUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row F ∨ hsame row S ∨ hsame row U ∨ hsame row Q ∨
              hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row firstRead ∨
                hsame row secondRead ∨ hsame row uniformRead ∨ hsame row regularRead ∨
                  hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont W F firstRead ∧ Cont W S secondRead ∧
              Cont U Q uniformRead ∧ Cont uniformRead R regularRead ∧
                Cont regularRead E sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
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
                              (Or.inr sourceRow.left)))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, firstRoute, secondRoute, uniformRoute, regularRoute, sealRoute,
          provenancePkg, sealPkg⟩
  }
  exact ⟨cert, firstUnary, secondUnary, uniformUnary, regularUnary, sealUnary⟩

end BEDC.Derived.MooreOsgoodUp
