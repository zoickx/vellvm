define i64 @main(i64 %argc, i8** %arcv) {
  %1 = add nuw i64 18446744073709551615, 100000
  ret i64 %1
}

