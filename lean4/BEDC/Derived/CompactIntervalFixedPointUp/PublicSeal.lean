import BEDC.Derived.CompactIntervalFixedPointUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactIntervalFixedPointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompactIntervalFixedPointCarrier [AskSetup] [PackageSetup]
    (J G R B W Q E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory J ∧ UnaryHistory G ∧ UnaryHistory R ∧ UnaryHistory B ∧
    UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
          ∃ packet : CompactIntervalFixedPointUp,
            packet = CompactIntervalFixedPointUp.mk J G R B W Q E H C P N

theorem CompactIntervalFixedPointPublicSeal [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactIntervalFixedPointCarrier J G R B W Q E H C P N bundle pkg →
      Cont B W Q →
        Cont Q E sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row sealRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨
                    hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row sealRead)
                (fun row : BHist =>
                  hsame row sealRead ∧ Cont B W Q ∧ Cont Q E sealRead ∧
                    PkgSig bundle sealRead pkg)
                hsame ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier windowRoute sealRoute sealPkg
  obtain ⟨_jUnary, _gUnary, _rUnary, bUnary, wUnary, _qUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _provenancePkg, _namePkg, _packetWitness⟩ := carrier
  have qUnary : UnaryHistory Q :=
    unary_cont_closed bUnary wUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row ∧
        PkgSig bundle row pkg) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary, sealPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row ∧
            PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨
              hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont B W Q ∧ Cont Q E sealRead ∧
              PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, windowRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp
