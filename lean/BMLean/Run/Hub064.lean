import BMLean.Tables
import BMLean.Data.Hub064

namespace BMC

theorem hubOk_064 : hubChunkOk (parseRows BMD.hub064) = true := by native_decide

end BMC
