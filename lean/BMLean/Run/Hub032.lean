import BMLean.Tables
import BMLean.Data.Hub032

namespace BMC

theorem hubOk_032 : hubChunkOk (parseRows BMD.hub032) = true := by native_decide

end BMC
