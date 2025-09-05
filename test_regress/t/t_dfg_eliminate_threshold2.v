module t(
  input  [1:0] in,
                output out);
  wire stl_initialized;
  wire [21:0] foo = $c(2);
  assign stl_initialized =
    foo == 1 | foo == 2 | foo == 3 | foo == 4 | foo == 5 | foo == 6 | foo == 7 |
    foo == 8 | foo == 9 | foo == 10 | foo == 11 | foo == 12 | foo == 13 | foo == 14 |
    foo == 15 | foo == 16 | foo == 17 | foo == 18 | foo == 19 | foo == 20 | foo == 21 |
    foo == 22 | foo == 23 | foo == 24 | foo == 25 | foo == 26 | foo == 27 | foo == 28 |
    foo == 29 | foo == 30 | foo == 31 | foo == 32 | foo == 33 | foo == 34 | foo == 35 |
    foo == 36 | foo == 37 | foo == 38 | foo == 39 | foo == 40 | foo == 41 | foo == 42 |
    foo == 43 | foo == 44 | foo == 45 | foo == 46 | foo == 47 | foo == 48 | foo == 49 |
    foo == 50 | foo == 51 | foo == 52 | foo == 53 | foo == 54 | foo == 55 | foo == 56 |
    foo == 57 | foo == 58 | foo == 59 | foo == 60 | foo == 61 | foo == 62 | foo == 63 |
    foo == 64 | foo == 65 | foo == 66 | foo == 67 | foo == 68 | foo == 69 | foo == 70 |
    foo == 71 | foo == 72 | foo == 73 | foo == 74 | foo == 75 | foo == 76 | foo == 77 |
    foo == 78 | foo == 79 | foo == 80 | foo == 81 | foo == 82 | foo == 83 | foo == 84 |
    foo == 85 | foo == 86 | foo == 87 | foo == 88 | foo == 89 | foo == 90 | foo == 91 |
    foo == 92 | foo == 93 | foo == 94 | foo == 95 | foo == 96 | foo == 97 | foo == 98 |
    foo == 99 | foo == 100 | foo == 101 | foo == 102 | foo == 103 | foo == 104 | foo == 105 |
    foo == 106 | foo == 107 | foo == 108 | foo == 109 | foo == 110 | foo == 111 | foo == 112 |
    foo == 113 | foo == 114 | foo == 115 | foo == 116 | foo == 117 | foo == 118 | foo == 119 |
    foo == 120 | foo == 121 | foo == 122 | foo == 123 | foo == 124 | foo == 125 | foo == 126 |
    foo == 127 | foo == 128 | foo == 129 | foo == 130 | foo == 131 | foo == 132 | foo == 133 |
    foo == 134 | foo == 135 | foo == 136 | foo == 137 | foo == 138 | foo == 139 | foo == 140 |
    foo == 141 | foo == 142 | foo == 143 | foo == 144 | foo == 145 | foo == 146 | foo == 147 |
    foo == 148 | foo == 149 | foo == 150 | foo == 151 | foo == 152 | foo == 153 | foo == 154 |
    foo == 155 | foo == 156 | foo == 157 | foo == 158 | foo == 159 | foo == 160 | foo == 161 |
    foo == 162 | foo == 163 | foo == 164 | foo == 165 | foo == 166 | foo == 167 | foo == 168 |
    foo == 169 | foo == 170 | foo == 171 | foo == 172 | foo == 173 | foo == 174 | foo == 175 |
    foo == 176 | foo == 177 | foo == 178 | foo == 179 | foo == 180 | foo == 181 | foo == 182 |
    foo == 183 | foo == 184 | foo == 185 | foo == 186 | foo == 187 | foo == 188 | foo == 189 |
    foo == 190 | foo == 191 | foo == 192 | foo == 193 | foo == 194 | foo == 195 | foo == 196 |
    foo == 197 | foo == 198 | foo == 199 | foo == 200 | foo == 201 | foo == 202 | foo == 203 |
    foo == 204 | foo == 205 | foo == 206 | foo == 207 | foo == 208 | foo == 209 | foo == 210 |
    foo == 211 | foo == 212 | foo == 213 | foo == 214 | foo == 215 | foo == 216 | foo == 217 |
    foo == 218 | foo == 219 | foo == 220 | foo == 221 | foo == 222 | foo == 223 | foo == 224 |
    foo == 225 | foo == 226 | foo == 227 | foo == 228 | foo == 229 | foo == 230 | foo == 231 |
    foo == 232 | foo == 233 | foo == 234 | foo == 235 | foo == 236 | foo == 237 | foo == 238 |
    foo == 239 | foo == 240 | foo == 241 | foo == 242 | foo == 243 | foo == 244 | foo == 245 |
    foo == 246 | foo == 247 | foo == 248 | foo == 249 | foo == 250 | foo == 251 | foo == 252 |
    foo == 253 | foo == 254 | foo == 255 | foo == 256 | foo == 257 | foo == 258 | foo == 259 |
    foo == 260 | foo == 261 | foo == 262 | foo == 263 | foo == 264 | foo == 265 | foo == 266 |
    foo == 267 | foo == 268 | foo == 269 | foo == 270 | foo == 271 | foo == 272 | foo == 273 |
    foo == 274 | foo == 275 | foo == 276 | foo == 277 | foo == 278 | foo == 279 | foo == 280 |
    foo == 281 | foo == 282 | foo == 283 | foo == 284 | foo == 285 | foo == 286 | foo == 287 |
    foo == 288 | foo == 289 | foo == 290 | foo == 291 | foo == 292 | foo == 293 | foo == 294 |
    foo == 295 | foo == 296 | foo == 297 | foo == 298 | foo == 299 | foo == 300 | foo == 301 |
    foo == 302 | foo == 303 | foo == 304 | foo == 305 | foo == 306 | foo == 307 | foo == 308 |
    foo == 309 | foo == 310 | foo == 311 | foo == 312 | foo == 313 | foo == 314 | foo == 315 |
    foo == 316 | foo == 317 | foo == 318 | foo == 319 | foo == 320 | foo == 321 | foo == 322 |
    foo == 323 | foo == 324 | foo == 325 | foo == 326 | foo == 327 | foo == 328 | foo == 329 |
    foo == 330 | foo == 331 | foo == 332 | foo == 333 | foo == 334 | foo == 335 | foo == 336 |
    foo == 337 | foo == 338 | foo == 339 | foo == 340 | foo == 341 | foo == 342 | foo == 343 |
    foo == 344 | foo == 345 | foo == 346 | foo == 347 | foo == 348 | foo == 349 | foo == 350 |
    foo == 351 | foo == 352 | foo == 353 | foo == 354 | foo == 355 | foo == 356 | foo == 357 |
    foo == 358 | foo == 359 | foo == 360 | foo == 361 | foo == 362 | foo == 363 | foo == 364 |
    foo == 365 | foo == 366 | foo == 367 | foo == 368 | foo == 369 | foo == 370 | foo == 371 |
    foo == 372 | foo == 373 | foo == 374 | foo == 375 | foo == 376 | foo == 377 | foo == 378 |
    foo == 379 | foo == 380 | foo == 381 | foo == 382 | foo == 383 | foo == 384 | foo == 385 |
    foo == 386 | foo == 387 | foo == 388 | foo == 389 | foo == 390 | foo == 391 | foo == 392 |
    foo == 393 | foo == 394 | foo == 395 | foo == 396 | foo == 397 | foo == 398 | foo == 399 |
    foo == 400 | foo == 401 | foo == 402 | foo == 403 | foo == 404 | foo == 405 | foo == 406 |
    foo == 407 | foo == 408 | foo == 409 | foo == 410 | foo == 411 | foo == 412 | foo == 413 |
    foo == 414 | foo == 415 | foo == 416 | foo == 417 | foo == 418 | foo == 419 | foo == 420 |
    foo == 421 | foo == 422 | foo == 423 | foo == 424 | foo == 425 | foo == 426 | foo == 427 |
    foo == 428 | foo == 429 | foo == 430 | foo == 431 | foo == 432 | foo == 433 | foo == 434 |
    foo == 435 | foo == 436 | foo == 437 | foo == 438 | foo == 439 | foo == 440 | foo == 441 |
    foo == 442 | foo == 443 | foo == 444 | foo == 445 | foo == 446 | foo == 447 | foo == 448 |
    foo == 449 | foo == 450 | foo == 451 | foo == 452 | foo == 453 | foo == 454 | foo == 455 |
    foo == 456 | foo == 457 | foo == 458 | foo == 459 | foo == 460 | foo == 461 | foo == 462 |
    foo == 463 | foo == 464 | foo == 465 | foo == 466 | foo == 467 | foo == 468 | foo == 469 |
    foo == 470 | foo == 471 | foo == 472 | foo == 473 | foo == 474 | foo == 475 | foo == 476 |
    foo == 477 | foo == 478 | foo == 479 | foo == 480 | foo == 481 | foo == 482 | foo == 483 |
    foo == 484 | foo == 485 | foo == 486 | foo == 487 | foo == 488 | foo == 489 | foo == 490 |
    foo == 491 | foo == 492 | foo == 493 | foo == 494 | foo == 495 | foo == 496 | foo == 497 |
    foo == 498 | foo == 499 | foo == 500 | foo == 501;
  wire [2:0] result = {{in[0] & stl_initialized}, {in}};
  assign out = result[in];
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
