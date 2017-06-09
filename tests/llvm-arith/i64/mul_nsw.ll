define i64 @main(i64 %argc, i8** %arcv) {
  %1 = mul nsw i64 18446744073709551614, -2
  ret i64 %1
}
