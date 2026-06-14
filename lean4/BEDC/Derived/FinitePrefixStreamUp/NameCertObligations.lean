import BEDC.Derived.FinitePrefixStreamUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FinitePrefixStreamCarrier (k W D R H C P N : BHist) : Prop :=
  UnaryHistory k ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
    UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append k W) ∧ Cont D R H ∧
      Cont H C P ∧ Cont P N (append (append k W) D)

theorem FinitePrefixStreamCarrier_namecert_obligations
    {k W D R H C P N windowRead regularRead : BHist} :
    FinitePrefixStreamCarrier k W D R H C P N ->
      Cont k W windowRead ->
        Cont windowRead D regularRead ->
          SemanticNameCert
              (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                  hsame row regularRead)
              (fun row : BHist => hsame row regularRead ∧ Cont windowRead D regularRead)
              hsame ∧
            UnaryHistory k ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
              UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                  hsame H (append k W) ∧ Cont k W windowRead ∧
                    Cont windowRead D regularRead ∧ Cont D R H ∧ Cont H C P ∧
                      Cont P N regularRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet windowRoute regularRoute
  obtain
    ⟨unaryK, unaryW, unaryD, unaryR, unaryC, unaryN, sameH, routeH, routeP,
      packetRegularRoute⟩ := packet
  have unaryH : UnaryHistory H :=
    unary_cont_closed unaryD unaryR routeH
  have unaryP : UnaryHistory P :=
    unary_cont_closed unaryH unaryC routeP
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryK unaryW windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary unaryD regularRoute
  have sameRegular : hsame (append (append k W) D) regularRead := by
    cases windowRoute
    exact hsame_symm regularRoute
  have localRoute : Cont P N regularRead :=
    cont_result_hsame_transport packetRegularRoute sameRegular
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row regularRead)
          (fun row : BHist => hsame row regularRead ∧ Cont windowRead D regularRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regularRead ⟨hsame_refl regularRead, regularUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, regularRoute⟩
  }
  exact
    ⟨cert, unaryK, unaryW, unaryD, unaryR, unaryH, unaryC, unaryN, windowUnary,
      regularUnary, sameH, windowRoute, regularRoute, routeH, routeP, localRoute⟩

theorem FinitePrefixStreamCarrier_obligation_surface [AskSetup] [PackageSetup]
    {depth window dyadic regular transport replay provenance localName prefixRead
      regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory depth →
      UnaryHistory window →
        UnaryHistory dyadic →
          UnaryHistory regular →
            UnaryHistory transport →
              UnaryHistory replay →
                Cont depth window prefixRead →
                  Cont prefixRead dyadic regularRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle localName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row depth ∨ hsame row window ∨ hsame row dyadic ∨
                                hsame row regular ∨ hsame row prefixRead ∨
                                  hsame row regularRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont depth window prefixRead ∧
                                Cont prefixRead dyadic regularRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                            hsame ∧
                          UnaryHistory prefixRead ∧ UnaryHistory regularRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro depthUnary windowUnary dyadicUnary _regularUnary _transportUnary _replayUnary
    depthWindowPrefixRead prefixReadDyadicRegularRead provenancePkg localNamePkg
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed depthUnary windowUnary depthWindowPrefixRead
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed prefixReadUnary dyadicUnary prefixReadDyadicRegularRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row depth ∨ hsame row window ∨ hsame row dyadic ∨
              hsame row regular ∨ hsame row prefixRead ∨ hsame row regularRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont depth window prefixRead ∧
              Cont prefixRead dyadic regularRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro regularRead ⟨hsame_refl regularRead, regularReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, depthWindowPrefixRead, prefixReadDyadicRegularRead, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, prefixReadUnary, regularReadUnary⟩

end BEDC.Derived.FinitePrefixStreamUp
