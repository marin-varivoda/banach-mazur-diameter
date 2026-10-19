import BMLean.Tables
import BMLean.Data.Hub008

namespace BMC

theorem hubOk_008 : hubChunkOk (parseRows BMD.hub008) = true := by native_decide

end BMC
