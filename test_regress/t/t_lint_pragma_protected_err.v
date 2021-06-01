module t_lint_pragma_protected_err;

// This part should see some failures

`pragma protect begin_protected
`pragma protect version="xx"
// should fail because value should be quoted
`pragma protect encrypt_agent=123
// should fail because no value given at all
`pragma protect encrypt_agent_info
`pragma protect data_method="AES128-CBC"
`pragma protect key_keyowner="BIG3#1"
`pragma protect key_keyname="AAAAAA"
`pragma protect key_method="RSA"

// expect error in key_block below, 64 bytes but expecting  65
// also expect "multiple `pragma encoding sections` error because number of
// bytes does not go down to 0 in the end of the section below due to the 64->65 change
`pragma protect encoding = (enctype = "BASE64", line_length = 76, bytes = 65)
`pragma protect key_block
ICAgICAgICAgICAgICAgICAgIEdOVSBMRVNTRVIgR0VORVJBTCBQVUJMSUMgTElDRU5TRQogICAg
KSAyMDA3IE==

`pragma protect key_keyowner="BIG3#2"
`pragma protect key_keyname="BBBBBB"
`pragma protect key_method="RSA"
`pragma protect encoding = (enctype = "BASE64", line_length = 76, bytes = 128)
`pragma protect key_block
IEV2ZXJ5b25lIGlzIHBlcm1pdHRlZCB0byBjb3B5IGFuZCBkaXN0cmlidXRlIHZlcmJhdGltIGNv
cGllcwogb2YgdGhpcyBsaWNlbnNlIGRvY3VtZW50LCBidXQgY2hhbmdpbmcgaXQgaXMgbm90IGFs
bG93ZWQuCgoKICBUaGl=

`pragma protect key_keyowner="BIG3#3"
`pragma protect key_keyname="CCCCCCCC"
`pragma protect key_method="RSA"
`pragma protect encoding = (enctype = "BASE64", line_length = 76, bytes = 128)
`pragma protect key_block
TGljZW5zZSBpbmNvcnBvcmF0ZXMKdGhlIHRlcm1zIGFuZCBjb25kaXRpb25zIG9mIHZlcnNpb24g
MyBvZiB0aGUgR05VIEdlbmVyYWwgUHVibGljCkxpY2Vuc2UsIHN1cHBsZW1lbnRlZCBieSB0aGUg
YWRkaXRpb25hbCBwZXJ=

`pragma protect encoding = (enctype = "BASE64", line_length = 76, bytes = 295)
`pragma protect data_block
aW5pdGlvbnMuCgogIEFzIHVzZWQgaGVyZWluLCAidGhpcyBMaWNlbnNlIiByZWZlcnMgdG8gdmVy
c2lvbiAzIG9mIHRoZSBHTlUgTGVzc2VyCkdlbmVyYWwgUHVibGljIExpY2Vuc2UsIGFuZCB0aGUg
IkdOVSBHUEwiIHJlZmVycyB0byB2ZXJzaW9uIDMgb2YgdGhlIEdOVQpHZW5lcmFsIFB1YmxpYyBM
aWNlbnNlLgoKICAiVGhlIExpYnJhcnkiIHJlZmVycyB0byBhIGNvdmVyZWQgd29yayBnb3Zlcm5l
ZCBieSB0aGlzIExpY2Vuc2UsCm90aGVyIHRoYW4gYW4gQXBwbGljYXRpb24gb3IgYSBDb21iaW5l
ZCBXb3JrIGFzIG==


`pragma protect end_protected

// Should trigger unknown pragma warning, although in principle unknown pragmas should be safely ignored.
`pragma XXXXX

// Should trigger missing pragma warning
`pragma

endmodule
