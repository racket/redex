(#rx"^ctc-fail: judgment input values do not match its contract;\n"
 ([bad-use (ctc-fail #t #f)])
 (test-judgment-holds bad-use))
