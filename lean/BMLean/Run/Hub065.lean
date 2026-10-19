import BMLean.Tables
import BMLean.Data.Hub065

namespace BMC

theorem hubOk_065 : hubChunkOk (parseRows BMD.hub065) = true := by native_decide

end BMC
