import BEDC.Derived.MetaCICAuditMapFamilyUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICAuditMapFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICAuditMapFamilyNonescape [AskSetup] [PackageSetup]
    {localMaps synthesisRows obstructionRows frontierRows dependencyLedger transports routes
      provenance localName consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    metaCICAuditMapFamilyFields
        (MetaCICAuditMapFamilyUp.mk localMaps synthesisRows obstructionRows frontierRows
          dependencyLedger transports routes provenance localName) =
        [localMaps, synthesisRows, obstructionRows, frontierRows, dependencyLedger, transports,
          routes, provenance, localName] →
      UnaryHistory localMaps → UnaryHistory dependencyLedger → UnaryHistory routes →
        Cont localMaps dependencyLedger consumerRead → PkgSig bundle provenance pkg →
          PkgSig bundle consumerRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row localMaps ∨ hsame row synthesisRows ∨
                    hsame row obstructionRows ∨ hsame row frontierRows ∨
                      hsame row dependencyLedger ∨ hsame row consumerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumerRead pkg)
                hsame ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fieldProjection unaryLocal unaryDependency _unaryRoutes consumerCont provenancePkg
    consumerPkg
  have projectedFields :
      metaCICAuditMapFamilyFields
          (MetaCICAuditMapFamilyUp.mk localMaps synthesisRows obstructionRows frontierRows
            dependencyLedger transports routes provenance localName) =
          [localMaps, synthesisRows, obstructionRows, frontierRows, dependencyLedger, transports,
            routes, provenance, localName] :=
    fieldProjection
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed unaryLocal unaryDependency consumerCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row localMaps ∨ hsame row synthesisRows ∨
              hsame row obstructionRows ∨ hsame row frontierRows ∨
                hsame row dependencyLedger ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      cases projectedFields
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.MetaCICAuditMapFamilyUp
