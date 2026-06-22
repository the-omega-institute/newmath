import BEDC.Derived.EffectiveCauchySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.EffectiveCauchySequenceUp.Nonescape

namespace BEDC.Derived.EffectiveCauchySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EffectiveCauchySequenceRealSealBoundary [AskSetup] [PackageSetup]
    {source modulus window dyadic readback realSeal transport replay provenance localName windowRead
      toleranceRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont source modulus windowRead →
      Cont windowRead window toleranceRead →
        Cont toleranceRead dyadic regularRead →
          Cont regularRead readback realSeal →
            Cont realSeal replay realRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle localName pkg →
                  UnaryHistory source →
                    UnaryHistory modulus →
                      UnaryHistory window →
                        UnaryHistory dyadic →
                          UnaryHistory readback →
                            UnaryHistory replay →
                              SemanticNameCert
                                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row source ∨ hsame row modulus ∨ hsame row window ∨
                                      hsame row dyadic ∨ hsame row readback ∨
                                        hsame row realSeal ∨ hsame row realRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont source modulus windowRead ∧
                                      Cont windowRead window toleranceRead ∧
                                        Cont toleranceRead dyadic regularRead ∧
                                          Cont realSeal replay realRead ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                                  UnaryHistory regularRead ∧ UnaryHistory realSeal ∧
                                    UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro windowRoute toleranceRoute regularRoute sealRoute realRoute provenancePkg localNamePkg
    sourceUnary modulusUnary windowUnary dyadicUnary readbackUnary replayUnary
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary modulusUnary windowRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowReadUnary windowUnary toleranceRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed toleranceReadUnary dyadicUnary regularRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regularReadUnary readbackUnary sealRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed realSealUnary replayUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row modulus ∨ hsame row window ∨ hsame row dyadic ∨
              hsame row readback ∨ hsame row realSeal ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source modulus windowRead ∧
              Cont windowRead window toleranceRead ∧ Cont toleranceRead dyadic regularRead ∧
                Cont realSeal replay realRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
                  (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, windowRoute, toleranceRoute, regularRoute, realRoute, provenancePkg,
          localNamePkg⟩
  }
  exact
    ⟨cert, windowReadUnary, toleranceReadUnary, regularReadUnary, realSealUnary, realReadUnary⟩

end BEDC.Derived.EffectiveCauchySequenceUp
