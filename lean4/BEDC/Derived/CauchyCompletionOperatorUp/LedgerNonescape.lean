import BEDC.Derived.CauchyCompletionOperatorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionOperatorPacket [AskSetup] [PackageSetup]
    (M B U S R D Q E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory U ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory Q ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont S R D ∧ Cont D Q E ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyCompletionOperatorLedgerNonescape [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorPacket M B U S R D Q E H C P N bundle pkg →
      Cont S R windowRead →
        Cont windowRead E sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row B ∨ hsame row U ∨ hsame row S ∨
                    hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row E ∨
                      hsame row sealRead)
                (fun row : BHist =>
                  hsame row sealRead ∧ Cont S R windowRead ∧
                    Cont windowRead E sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧ UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet streamRegularWindow windowSeal sealPkg
  obtain ⟨_metricUnary, _boundaryUnary, _uniformUnary, streamUnary, regularUnary,
    _dyadicUnary, _separatedUnary, realSealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary regularUnary streamRegularWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary realSealUnary windowSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row B ∨ hsame row U ∨ hsame row S ∨
              hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row E ∨
                hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont S R windowRead ∧
              Cont windowRead E sealRead ∧ PkgSig bundle sealRead pkg)
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, streamRegularWindow, windowSeal, sealPkg⟩
  }
  exact ⟨cert, windowUnary, sealUnary⟩

end BEDC.Derived.CauchyCompletionOperatorUp
