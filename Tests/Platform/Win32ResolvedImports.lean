import Grass.Platform.Win32.Target.ImportTable

/-! Model-unit checks for unique resolved Win32 imports. These supplied
bindings do not claim correspondence with a native loader or OS provider. -/

namespace Grass.Tests.Win32ResolvedImports

open Grass.Platform.Win32.Target

private def check (label : String) (passed : Bool) : IO Unit :=
  unless passed do
    throw (IO.userError ("resolved import fixture failed: " ++ label))

def exitSymbol : Grass.Target.ImportSymbol :=
  { library := "KERNEL32.dll", symbol := "ExitProcess", slotAddress := 0x2040 }

def exitBinding : ResolvedImport :=
  { importSymbol := exitSymbol, targetAddress := 0x7ff812345678 }

def otherSlot : ResolvedImport :=
  { importSymbol := { exitSymbol with slotAddress := 0x2050 }
    targetAddress := 0x7ff887654321 }

def conflicting : ResolvedImport :=
  { importSymbol := { exitSymbol with symbol := "WriteFile" }
    targetAddress := 0x7ff800001111 }

def unknownLibrary : ResolvedImport :=
  { importSymbol := { exitSymbol with library := "MODEL.dll" }
    targetAddress := exitBinding.targetAddress }

def unknownSymbol : ResolvedImport :=
  { importSymbol := { exitSymbol with symbol := "exitprocess" }
    targetAddress := exitBinding.targetAddress }

#eval check "exact ExitProcess binding"
  (resolvedApiOf [otherSlot, exitBinding] exitSymbol.slotAddress exitBinding.targetAddress ==
    some .exitProcess)

#eval check "altered loaded target rejected"
  (resolvedApiOf [exitBinding] exitSymbol.slotAddress (exitBinding.targetAddress + 1) == none)

#eval check "absent slot rejected"
  (resolvedApiOf [otherSlot] exitSymbol.slotAddress exitBinding.targetAddress == none)

#eval check "duplicate conflicting slot rejected"
  (resolvedApiOf [exitBinding, conflicting] exitSymbol.slotAddress exitBinding.targetAddress == none)

#eval check "zero resolved target rejected"
  (resolvedApiOf [{ exitBinding with targetAddress := 0 }] exitSymbol.slotAddress 0 == none)

#eval check "unknown library rejected"
  (resolvedApiOf [unknownLibrary] exitSymbol.slotAddress exitBinding.targetAddress == none)

#eval check "unknown symbol rejected"
  (resolvedApiOf [unknownSymbol] exitSymbol.slotAddress exitBinding.targetAddress == none)

example : ∃ binding,
    [otherSlot, exitBinding].filter
      (fun candidate => candidate.importSymbol.slotAddress == exitSymbol.slotAddress) = [binding] ∧
    binding.targetAddress = exitBinding.targetAddress ∧ binding.targetAddress ≠ 0 := by
  apply resolvedApiOf_binding
    (api := Api.exitProcess)
  decide

end Grass.Tests.Win32ResolvedImports
