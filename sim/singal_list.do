onerror resume
wave tags F0 
wave update off
wave zoom range 0 571760
wave add ahb_axi4_tb.dut.clk -tag F0 -radix hexadecimal -foregroundcolor Green
wave add ahb_axi4_tb.dut.rst_n -tag F0 -radix hexadecimal -foregroundcolor Green
wave add ahb_axi4_tb.dut.HWRITE -tag F0 -radix hexadecimal -foregroundcolor Green
wave group WRITE -backgroundcolor #006666
wave group WRITE:AHB -backgroundcolor #004466
wave add -group WRITE:AHB ahb_axi4_tb.HTRANS -tag F0 -radix mnemonic -foregroundcolor Green
wave add -group WRITE:AHB ahb_axi4_tb.dut.HADDR -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:AHB ahb_axi4_tb.dut.HWDATA -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:AHB ahb_axi4_tb.dut.HREADY -tag F0 -radix hexadecimal -foregroundcolor Green
wave insertion [expr [wave index insertpoint] + 1]
wave spacer -group WRITE {}
wave group WRITE:ADDR -backgroundcolor #226600
wave add -group WRITE:ADDR ahb_axi4_tb.dut.HADDR -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:ADDR ahb_axi4_tb.dut.AWADDR -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:ADDR ahb_axi4_tb.dut.AWVALID -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:ADDR ahb_axi4_tb.dut.AWREADY -tag F0 -radix hexadecimal -foregroundcolor Green
wave spacer -group WRITE:ADDR {}
wave insertion [expr [wave index insertpoint] + 1]
wave group WRITE:DATA -backgroundcolor #666600
wave add -group WRITE:DATA ahb_axi4_tb.dut.HWDATA -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:DATA ahb_axi4_tb.dut.WDATA -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:DATA ahb_axi4_tb.dut.WVALID -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:DATA ahb_axi4_tb.dut.WREADY -tag F0 -radix hexadecimal -foregroundcolor Green
wave spacer -group WRITE:DATA {}
wave insertion [expr [wave index insertpoint] + 1]
wave group WRITE:RESP -backgroundcolor #664400
wave add -group WRITE:RESP ahb_axi4_tb.dut.WLAST -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:RESP ahb_axi4_tb.dut.BVALID -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:RESP ahb_axi4_tb.dut.BREADY -tag F0 -radix hexadecimal -foregroundcolor Green
wave add -group WRITE:RESP ahb_axi4_tb.BRESP -tag F0 -radix mnemonic -foregroundcolor Green
wave add -group WRITE:RESP ahb_axi4_tb.dut.HRESP -tag F0 -radix hexadecimal -foregroundcolor Green
wave insertion [expr [wave index insertpoint] + 1]
wave spacer -group WRITE {}
wave insertion [expr [wave index insertpoint] + 1]
wave group READ -backgroundcolor #660000
wave group READ:AHB -backgroundcolor #660066
wave add -group READ:AHB ahb_axi4_tb.HTRANS -tag F0 -radix mnemonic
wave add -group READ:AHB ahb_axi4_tb.dut.HADDR -tag F0 -radix hexadecimal
wave add -group READ:AHB ahb_axi4_tb.dut.HRDATA -tag F0 -radix hexadecimal
wave add -group READ:AHB ahb_axi4_tb.dut.HREADY -tag F0 -radix hexadecimal
wave add -group READ:AHB ahb_axi4_tb.HTRANS -tag F0 -radix mnemonic
wave add -group READ:AHB ahb_axi4_tb.dut.HADDR -tag F0 -radix hexadecimal
wave add -group READ:AHB ahb_axi4_tb.dut.HRDATA -tag F0 -radix hexadecimal
wave add -group READ:AHB ahb_axi4_tb.dut.HREADY -tag F0 -radix hexadecimal
wave group READ:ADDR -backgroundcolor #440066
wave add -group READ:ADDR ahb_axi4_tb.dut.HADDR -tag F0 -radix hexadecimal
wave add -group READ:ADDR ahb_axi4_tb.dut.ARADDR -tag F0 -radix hexadecimal
wave add -group READ:ADDR ahb_axi4_tb.dut.ARVALID -tag F0 -radix hexadecimal
wave add -group READ:ADDR ahb_axi4_tb.dut.ARREADY -tag F0 -radix hexadecimal
wave add -group READ:ADDR ahb_axi4_tb.dut.HADDR -tag F0 -radix hexadecimal
wave add -group READ:ADDR ahb_axi4_tb.dut.ARADDR -tag F0 -radix hexadecimal
wave add -group READ:ADDR ahb_axi4_tb.dut.ARVALID -tag F0 -radix hexadecimal
wave add -group READ:ADDR ahb_axi4_tb.dut.ARREADY -tag F0 -radix hexadecimal
wave group READ:DATA -backgroundcolor #004466
wave add -group READ:DATA ahb_axi4_tb.dut.RREADY -tag F0 -radix hexadecimal
wave add -group READ:DATA ahb_axi4_tb.dut.RVALID -tag F0 -radix hexadecimal
wave add -group READ:DATA ahb_axi4_tb.dut.HRDATA -tag F0 -radix hexadecimal
wave add -group READ:DATA ahb_axi4_tb.dut.RDATA -tag F0 -radix hexadecimal
wave add -group READ:DATA ahb_axi4_tb.dut.RLAST -tag F0 -radix hexadecimal
wave add -group READ:DATA ahb_axi4_tb.dut.RREADY -tag F0 -radix hexadecimal
wave add -group READ:DATA ahb_axi4_tb.dut.RVALID -tag F0 -radix hexadecimal
wave add -group READ:DATA ahb_axi4_tb.dut.HRDATA -tag F0 -radix hexadecimal
wave add -group READ:DATA ahb_axi4_tb.dut.RDATA -tag F0 -radix hexadecimal
wave add -group READ:DATA ahb_axi4_tb.dut.RLAST -tag F0 -radix hexadecimal
wave group READ:RESP -backgroundcolor #006666
wave add -group READ:RESP ahb_axi4_tb.dut.RRESP -tag F0 -radix hexadecimal
wave add -group READ:RESP ahb_axi4_tb.dut.HRESP -tag F0 -radix hexadecimal
wave add -group READ:RESP ahb_axi4_tb.dut.RRESP -tag F0 -radix hexadecimal
wave add -group READ:RESP ahb_axi4_tb.dut.HRESP -tag F0 -radix hexadecimal
wave add -group READ:RESP ahb_axi4_tb.dut.RRESP -tag F0 -radix hexadecimal
wave add -group READ:RESP ahb_axi4_tb.dut.HRESP -tag F0 -radix hexadecimal
wave add -group READ:RESP ahb_axi4_tb.dut.RRESP -tag F0 -radix hexadecimal
wave add -group READ:RESP ahb_axi4_tb.dut.HRESP -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group READ -collapse
wave update on
wave top 0
