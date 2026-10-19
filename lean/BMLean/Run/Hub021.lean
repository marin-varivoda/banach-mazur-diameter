import BMLean.Tables
import BMLean.Data.Hub021

namespace BMC

theorem hubOk_021 : hubChunkOk (parseRows BMD.hub021) = true := by native_decide

end BMC
