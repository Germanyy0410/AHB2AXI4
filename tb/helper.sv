task automatic c1;
  begin
      @(posedge clk);
      #0.1;
  end
endtask

task automatic c2;
  begin
    @(negedge clk);
    #0.1;
  end
endtask

task automatic c3;
  begin
    #0.1;
  end
endtask