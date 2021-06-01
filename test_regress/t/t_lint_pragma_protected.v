// This part should pass OK

module t_lint_pragma_protected;

`pragma protect begin_protected
`pragma protect version=1
`pragma protect encrypt_agent="XXXXX"
`pragma protect encrypt_agent_info="YYYYY"
`pragma protect data_method="AES128-CBC"
`pragma protect key_keyowner="BIG3#1"
`pragma protect key_keyname="AAAAAA"
`pragma protect key_method="RSA"
`pragma protect encoding = (enctype = "BASE64", line_length = 76, bytes = 64)
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

endmodule
