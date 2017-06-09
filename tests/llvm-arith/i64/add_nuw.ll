define i64 @main(i64 %argc, i8** %arcv) {
  %1 = add nuw i64 -9223372036854775808, 100
  ret i64 %1
}

