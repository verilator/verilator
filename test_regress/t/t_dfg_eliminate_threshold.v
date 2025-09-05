// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (
    input [1:0] in,
    input [31:0] foo,
    output [1:0] out
);
  wire        stl_initialized;
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
    foo == 498 | foo == 499 | foo == 500 | foo == 501 | foo == 502 | foo == 503 | foo == 504 |
    foo == 505 | foo == 506 | foo == 507 | foo == 508 | foo == 509 | foo == 510 | foo == 511 |
    foo == 512 | foo == 513 | foo == 514 | foo == 515 | foo == 516 | foo == 517 | foo == 518 |
    foo == 519 | foo == 520 | foo == 521 | foo == 522 | foo == 523 | foo == 524 | foo == 525 |
    foo == 526 | foo == 527 | foo == 528 | foo == 529 | foo == 530 | foo == 531 | foo == 532 |
    foo == 533 | foo == 534 | foo == 535 | foo == 536 | foo == 537 | foo == 538 | foo == 539 |
    foo == 540 | foo == 541 | foo == 542 | foo == 543 | foo == 544 | foo == 545 | foo == 546 |
    foo == 547 | foo == 548 | foo == 549 | foo == 550 | foo == 551 | foo == 552 | foo == 553 |
    foo == 554 | foo == 555 | foo == 556 | foo == 557 | foo == 558 | foo == 559 | foo == 560 |
    foo == 561 | foo == 562 | foo == 563 | foo == 564 | foo == 565 | foo == 566 | foo == 567 |
    foo == 568 | foo == 569 | foo == 570 | foo == 571 | foo == 572 | foo == 573 | foo == 574 |
    foo == 575 | foo == 576 | foo == 577 | foo == 578 | foo == 579 | foo == 580 | foo == 581 |
    foo == 582 | foo == 583 | foo == 584 | foo == 585 | foo == 586 | foo == 587 | foo == 588 |
    foo == 589 | foo == 590 | foo == 591 | foo == 592 | foo == 593 | foo == 594 | foo == 595 |
    foo == 596 | foo == 597 | foo == 598 | foo == 599 | foo == 600 | foo == 601 | foo == 602 |
    foo == 603 | foo == 604 | foo == 605 | foo == 606 | foo == 607 | foo == 608 | foo == 609 |
    foo == 610 | foo == 611 | foo == 612 | foo == 613 | foo == 614 | foo == 615 | foo == 616 |
    foo == 617 | foo == 618 | foo == 619 | foo == 620 | foo == 621 | foo == 622 | foo == 623 |
    foo == 624 | foo == 625 | foo == 626 | foo == 627 | foo == 628 | foo == 629 | foo == 630 |
    foo == 631 | foo == 632 | foo == 633 | foo == 634 | foo == 635 | foo == 636 | foo == 637 |
    foo == 638 | foo == 639 | foo == 640 | foo == 641 | foo == 642 | foo == 643 | foo == 644 |
    foo == 645 | foo == 646 | foo == 647 | foo == 648 | foo == 649 | foo == 650 | foo == 651 |
    foo == 652 | foo == 653 | foo == 654 | foo == 655 | foo == 656 | foo == 657 | foo == 658 |
    foo == 659 | foo == 660 | foo == 661 | foo == 662 | foo == 663 | foo == 664 | foo == 665 |
    foo == 666 | foo == 667 | foo == 668 | foo == 669 | foo == 670 | foo == 671 | foo == 672 |
    foo == 673 | foo == 674 | foo == 675 | foo == 676 | foo == 677 | foo == 678 | foo == 679 |
    foo == 680 | foo == 681 | foo == 682 | foo == 683 | foo == 684 | foo == 685 | foo == 686 |
    foo == 687 | foo == 688 | foo == 689 | foo == 690 | foo == 691 | foo == 692 | foo == 693 |
    foo == 694 | foo == 695 | foo == 696 | foo == 697 | foo == 698 | foo == 699 | foo == 700 |
    foo == 701 | foo == 702 | foo == 703 | foo == 704 | foo == 705 | foo == 706 | foo == 707 |
    foo == 708 | foo == 709 | foo == 710 | foo == 711 | foo == 712 | foo == 713 | foo == 714 |
    foo == 715 | foo == 716 | foo == 717 | foo == 718 | foo == 719 | foo == 720 | foo == 721 |
    foo == 722 | foo == 723 | foo == 724 | foo == 725 | foo == 726 | foo == 727 | foo == 728 |
    foo == 729 | foo == 730 | foo == 731 | foo == 732 | foo == 733 | foo == 734 | foo == 735 |
    foo == 736 | foo == 737 | foo == 738 | foo == 739 | foo == 740 | foo == 741 | foo == 742 |
    foo == 743 | foo == 744 | foo == 745 | foo == 746 | foo == 747 | foo == 748 | foo == 749 |
    foo == 750 | foo == 751 | foo == 752 | foo == 753 | foo == 754 | foo == 755 | foo == 756 |
    foo == 757 | foo == 758 | foo == 759 | foo == 760 | foo == 761 | foo == 762 | foo == 763 |
    foo == 764 | foo == 765 | foo == 766 | foo == 767 | foo == 768 | foo == 769 | foo == 770 |
    foo == 771 | foo == 772 | foo == 773 | foo == 774 | foo == 775 | foo == 776 | foo == 777 |
    foo == 778 | foo == 779 | foo == 780 | foo == 781 | foo == 782 | foo == 783 | foo == 784 |
    foo == 785 | foo == 786 | foo == 787 | foo == 788 | foo == 789 | foo == 790 | foo == 791 |
    foo == 792 | foo == 793 | foo == 794 | foo == 795 | foo == 796 | foo == 797 | foo == 798 |
    foo == 799 | foo == 800 | foo == 801 | foo == 802 | foo == 803 | foo == 804 | foo == 805 |
    foo == 806 | foo == 807 | foo == 808 | foo == 809 | foo == 810 | foo == 811 | foo == 812 |
    foo == 813 | foo == 814 | foo == 815 | foo == 816 | foo == 817 | foo == 818 | foo == 819 |
    foo == 820 | foo == 821 | foo == 822 | foo == 823 | foo == 824 | foo == 825 | foo == 826 |
    foo == 827 | foo == 828 | foo == 829 | foo == 830 | foo == 831 | foo == 832 | foo == 833 |
    foo == 834 | foo == 835 | foo == 836 | foo == 837 | foo == 838 | foo == 839 | foo == 840 |
    foo == 841 | foo == 842 | foo == 843 | foo == 844 | foo == 845 | foo == 846 | foo == 847 |
    foo == 848 | foo == 849 | foo == 850 | foo == 851 | foo == 852 | foo == 853 | foo == 854 |
    foo == 855 | foo == 856 | foo == 857 | foo == 858 | foo == 859 | foo == 860 | foo == 861 |
    foo == 862 | foo == 863 | foo == 864 | foo == 865 | foo == 866 | foo == 867 | foo == 868 |
    foo == 869 | foo == 870 | foo == 871 | foo == 872 | foo == 873 | foo == 874 | foo == 875 |
    foo == 876 | foo == 877 | foo == 878 | foo == 879 | foo == 880 | foo == 881 | foo == 882 |
    foo == 883 | foo == 884 | foo == 885 | foo == 886 | foo == 887 | foo == 888 | foo == 889 |
    foo == 890 | foo == 891 | foo == 892 | foo == 893 | foo == 894 | foo == 895 | foo == 896 |
    foo == 897 | foo == 898 | foo == 899 | foo == 900 | foo == 901 | foo == 902 | foo == 903 |
    foo == 904 | foo == 905 | foo == 906 | foo == 907 | foo == 908 | foo == 909 | foo == 910 |
    foo == 911 | foo == 912 | foo == 913 | foo == 914 | foo == 915 | foo == 916 | foo == 917 |
    foo == 918 | foo == 919 | foo == 920 | foo == 921 | foo == 922 | foo == 923 | foo == 924 |
    foo == 925 | foo == 926 | foo == 927 | foo == 928 | foo == 929 | foo == 930 | foo == 931 |
    foo == 932 | foo == 933 | foo == 934 | foo == 935 | foo == 936 | foo == 937 | foo == 938 |
    foo == 939 | foo == 940 | foo == 941 | foo == 942 | foo == 943 | foo == 944 | foo == 945 |
    foo == 946 | foo == 947 | foo == 948 | foo == 949 | foo == 950 | foo == 951 | foo == 952 |
    foo == 953 | foo == 954 | foo == 955 | foo == 956 | foo == 957 | foo == 958 | foo == 959 |
    foo == 960 | foo == 961 | foo == 962 | foo == 963 | foo == 964 | foo == 965 | foo == 966 |
    foo == 967 | foo == 968 | foo == 969 | foo == 970 | foo == 971 | foo == 972 | foo == 973 |
    foo == 974 | foo == 975 | foo == 976 | foo == 977 | foo == 978 | foo == 979 | foo == 980 |
    foo == 981 | foo == 982 | foo == 983 | foo == 984 | foo == 985 | foo == 986 | foo == 987 |
    foo == 988 | foo == 989 | foo == 990 | foo == 991 | foo == 992 | foo == 993 | foo == 994 |
    foo == 995 | foo == 996 | foo == 997 | foo == 998 | foo == 999 | foo == 1000;

  wire [1:0] depends_on_input = {
    {
      in[0] & stl_initialized
    },
    {
      in[0]
    }
  };

  assign out = depends_on_input & in;

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
