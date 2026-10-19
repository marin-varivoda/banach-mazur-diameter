import BMLean.Tables
import BMLean.Data.Hub023

namespace BMC

theorem hubOk_023 : hubChunkOk (parseRows BMD.hub023) = true := by native_decide

end BMC
