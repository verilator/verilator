/*
 * Copyright (c) 2003-2016 Tony Bybell.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#ifdef _AIX
#pragma alloca
#endif

#include "lxt2_config.h"
#include "lxt2_write.h"

static char *lxt2_wr_vcd_truncate_bitvec(char *s)
{
char l, r;

r=*s;
if(r=='1')
        {
        return s;
        }
        else
        {
        s++;
        }

for(;;s++)
        {
        l=r; r=*s;
        if(!r) return (s-1);

        if(l!=r)
                {
                return(((l=='0')&&(r=='1'))?s:s-1);
                }
        }
}


/*
 * in-place sort to keep chained facs from migrating...
 */
static void wave_mergesort(struct lxt2_wr_symbol **a, struct lxt2_wr_symbol **b, int lo, int hi)
{
int i, j, k;

if (lo<hi)
	{
        int mid=(lo+hi)/2;

        wave_mergesort(a, b, lo, mid);
        wave_mergesort(a, b, mid+1, hi);

    	i=0; j=lo;
    	while (j<=mid)
		{
        	b[i++]=a[j++];
		}

    	i=0; k=lo;
    	while ((k<j)&&(j<=hi))
		{
        	if (strcmp(b[i]->name, a[j]->name) <= 0)
			{
            		a[k++]=b[i++];
			}
			else
			{
	            	a[k++]=a[j++];
			}
		}

    	while (k<j)
		{
        	a[k++]=b[i++];
		}
	}
}

static void wave_msort(struct lxt2_wr_symbol **a, int num)
{
struct lxt2_wr_symbol **b = (lxt2_wr_symbol**)malloc(((num/2)+1) * sizeof(struct lxt2_wr_symbol *));

wave_mergesort(a, b, 0, num-1);

free(b);
}

/************************ splay ************************/

static lxt2_wr_ds_Tree * lxt2_wr_ds_splay (granmsk_t i, lxt2_wr_ds_Tree * t) {
/* Simple top down splay, not requiring i to be in the tree t.  */
/* What it does is described above.                             */
    lxt2_wr_ds_Tree N, *l, *r, *y;
    if (t == NULL) return t;
    N.left = N.right = NULL;
    l = r = &N;

    for (;;) {
	if (i < t->item) {
	    if (t->left == NULL) break;
	    if (i < t->left->item) {
		y = t->left;                           /* rotate right */
		t->left = y->right;
		y->right = t;
		t = y;
		if (t->left == NULL) break;
	    }
	    r->left = t;                               /* link right */
	    r = t;
	    t = t->left;
	} else if (i > t->item) {
	    if (t->right == NULL) break;
	    if (i > t->right->item) {
		y = t->right;                          /* rotate left */
		t->right = y->left;
		y->left = t;
		t = y;
		if (t->right == NULL) break;
	    }
	    l->right = t;                              /* link left */
	    l = t;
	    t = t->right;
	} else {
	    break;
	}
    }
    l->right = t->left;                                /* assemble */
    r->left = t->right;
    t->left = N.right;
    t->right = N.left;
    return t;
}


static lxt2_wr_ds_Tree * lxt2_wr_ds_insert(granmsk_t i, lxt2_wr_ds_Tree * t, int val) {
/* Insert i into the tree t, unless it's already there.    */
/* Return a pointer to the resulting tree.                 */
    lxt2_wr_ds_Tree * n;

    n = (lxt2_wr_ds_Tree *) calloc (1, sizeof (lxt2_wr_ds_Tree));
    if (n == NULL) {
	fprintf(stderr, "ds_insert: ran out of memory, exiting.\n");
	exit(255);
    }
    n->item = i;
    n->val = val;
    if (t == NULL) {
	n->left = n->right = NULL;
	return n;
    }
    t = lxt2_wr_ds_splay(i,t);
    if (i < t->item) {
	n->left = t->left;
	n->right = t;
	t->left = NULL;
	return n;
    } else if (i > t->item) {
	n->right = t->right;
	n->left = t;
	t->right = NULL;
	return n;
    } else { /* We get here if it's already in the tree */
             /* Don't add it again                      */
	free(n);
	return t;
    }
}

/************************ splay ************************/

static int lxt2_wr_dslxt_success;

static lxt2_wr_dslxt_Tree * lxt2_wr_dslxt_splay (char *i, lxt2_wr_dslxt_Tree * t) {
/* Simple top down splay, not requiring i to be in the tree t.  */
/* What it does is described above.                             */
    lxt2_wr_dslxt_Tree N, *l, *r, *y;
    int dir;

    lxt2_wr_dslxt_success = 0;

    if (t == NULL) return t;
    N.left = N.right = NULL;
    l = r = &N;

    for (;;) {
	dir = strcmp(i, t->item);
	if (dir < 0) {
	    if (t->left == NULL) break;
	    if (strcmp(i, t->left->item)<0) {
		y = t->left;                           /* rotate right */
		t->left = y->right;
		y->right = t;
		t = y;
		if (t->left == NULL) break;
	    }
	    r->left = t;                               /* link right */
	    r = t;
	    t = t->left;
	} else if (dir > 0) {
	    if (t->right == NULL) break;
	    if (strcmp(i, t->right->item)>0) {
		y = t->right;                          /* rotate left */
		t->right = y->left;
		y->left = t;
		t = y;
		if (t->right == NULL) break;
	    }
	    l->right = t;                              /* link left */
	    l = t;
	    t = t->right;
	} else {
	    lxt2_wr_dslxt_success=1;
	    break;
	}
    }
    l->right = t->left;                                /* assemble */
    r->left = t->right;
    t->left = N.right;
    t->right = N.left;
    return t;
}


static lxt2_wr_dslxt_Tree * lxt2_wr_dslxt_insert(char *i, lxt2_wr_dslxt_Tree * t, unsigned int val) {
/* Insert i into the tree t, unless it's already there.    */
/* Return a pointer to the resulting tree.                 */
    lxt2_wr_dslxt_Tree * n;
    int dir;

    n = (lxt2_wr_dslxt_Tree *) calloc (1, sizeof (lxt2_wr_dslxt_Tree));
    if (n == NULL) {
	fprintf(stderr, "dslxt_insert: ran out of memory, exiting.\n");
	exit(255);
    }
    n->item = i;
    n->val  = val;
    if (t == NULL) {
	n->left = n->right = NULL;
	return n;
    }
    t = lxt2_wr_dslxt_splay(i,t);
    dir = strcmp(i,t->item);
    if (dir<0) {
	n->left = t->left;
	n->right = t;
	t->left = NULL;
	return n;
    } else if (dir>0) {
	n->right = t->right;
	n->left = t;
	t->right = NULL;
	return n;
    } else { /* We get here if it's already in the tree */
             /* Don't add it again                      */
	free(n);
	return t;
    }
}

/************************ splay ************************/

/*
 * functions which emit various big endian
 * data to a file
 */
static int lxt2_wr_emit_u8(struct lxt2_wr_trace *lt, int value)
{
unsigned char buf[1];
int nmemb;

buf[0] = value & 0xff;
nmemb=fwrite(buf, sizeof(char), 1, lt->handle);
lt->position+=nmemb;
return(nmemb);
}


static int lxt2_wr_emit_u16(struct lxt2_wr_trace *lt, int value)
{
unsigned char buf[2];
int nmemb;

buf[0] = (value>>8) & 0xff;
buf[1] = value & 0xff;
nmemb = fwrite(buf, sizeof(char), 2, lt->handle);
lt->position+=nmemb;
return(nmemb);
}


static int lxt2_wr_emit_u32(struct lxt2_wr_trace *lt, int value)
{
unsigned char buf[4];
int nmemb;

buf[0] = (value>>24) & 0xff;
buf[1] = (value>>16) & 0xff;
buf[2] = (value>>8) & 0xff;
buf[3] = value & 0xff;
nmemb=fwrite(buf, sizeof(char), 4, lt->handle);
lt->position+=nmemb;
return(nmemb);
}


static int lxt2_wr_emit_u64(struct lxt2_wr_trace *lt, int valueh, int valuel)
{
int rc;

if((rc=lxt2_wr_emit_u32(lt, valueh)))
	{
	rc=lxt2_wr_emit_u32(lt, valuel);
	}

return(rc);
}


/*
 * gzfunctions which emit various big endian
 * data to a file.  (lt->position needs to be
 * fixed up on gzclose so the tables don't
 * get out of sync!)
 */
static int gzwrite_buffered(struct lxt2_wr_trace *lt)
{
int rc = 1;

if(lt->gzbufpnt > LXT2_WR_GZWRITE_BUFFER)
	{
	rc = gzwrite(lt->zhandle, lt->gzdest, lt->gzbufpnt);
	rc = rc ? 1 : 0;
	lt->gzbufpnt = 0;
	}

return(rc);
}

static void gzflush_buffered(struct lxt2_wr_trace *lt, int doclose)
{
if(lt->gzbufpnt)
	{
	gzwrite(lt->zhandle, lt->gzdest, lt->gzbufpnt);
	lt->gzbufpnt = 0;
	if(!doclose)
		{
		gzflush(lt->zhandle, Z_SYNC_FLUSH);
		}
	}

if(doclose)
	{
	gzclose(lt->zhandle);
	}
}


static int lxt2_wr_emit_u8z(struct lxt2_wr_trace *lt, int value)
{
int nmemb;

lt->gzdest[lt->gzbufpnt++] = value & 0xff;

nmemb=gzwrite_buffered(lt);
lt->zpackcount++;
lt->position++;
return(nmemb);
}


static int lxt2_wr_emit_u16z(struct lxt2_wr_trace *lt, int value)
{
int nmemb;

lt->gzdest[lt->gzbufpnt++] = (value>>8) & 0xff;
lt->gzdest[lt->gzbufpnt++] = value & 0xff;
nmemb = gzwrite_buffered(lt);
lt->zpackcount+=2;
lt->position+=2;
return(nmemb);
}


static int lxt2_wr_emit_u24z(struct lxt2_wr_trace *lt, int value)
{
int nmemb;

lt->gzdest[lt->gzbufpnt++] = (value>>16) & 0xff;
lt->gzdest[lt->gzbufpnt++] = (value>>8) & 0xff;
lt->gzdest[lt->gzbufpnt++] = value & 0xff;
nmemb=gzwrite_buffered(lt);
lt->zpackcount+=3;
lt->position+=3;
return(nmemb);
}


static int lxt2_wr_emit_u32z(struct lxt2_wr_trace *lt, int value)
{
int nmemb;

lt->gzdest[lt->gzbufpnt++] = (value>>24) & 0xff;
lt->gzdest[lt->gzbufpnt++] = (value>>16) & 0xff;
lt->gzdest[lt->gzbufpnt++] = (value>>8) & 0xff;
lt->gzdest[lt->gzbufpnt++] = value & 0xff;
nmemb=gzwrite_buffered(lt);

lt->zpackcount+=4;
lt->position+=4;
return(nmemb);
}


static int lxt2_wr_emit_u64z(struct lxt2_wr_trace *lt, int valueh, int valuel)
{
int rc;

if((rc=lxt2_wr_emit_u32z(lt, valueh)))
	{
	rc=lxt2_wr_emit_u32z(lt, valuel);
	}

return(rc);
}


static int lxt2_wr_emit_stringz(struct lxt2_wr_trace *lt, char *value)
{
int rc=1;
do
	{
        rc&=lxt2_wr_emit_u8z(lt, *value);
        } while(*(value++));
return(rc);
}


/*
 * hash/symtable manipulation
 */
static int lxt2_wr_hash(const char *s)
{
const char *p;
char ch;
unsigned int h=0, h2=0, pos=0, g;
for(p=s;*p;p++)
        {
	ch=*p;
	h2<<=3;
	h2-=((unsigned int)ch+(pos++));		/* this handles stranded vectors quite well.. */

        h=(h<<4)+ch;
        if((g=h&0xf0000000))
                {
                h=h^(g>>24);
                h=h^g;
                }
        }

h^=h2;						/* combine the two hashes */
return(h%LXT2_WR_SYMPRIME);
}


static struct lxt2_wr_symbol *lxt2_wr_symadd(struct lxt2_wr_trace *lt, const char *name, int hv)
{
struct lxt2_wr_symbol *s;

s=(struct lxt2_wr_symbol *)calloc(1,sizeof(struct lxt2_wr_symbol));
strcpy(s->name=(char *)malloc((s->namlen=strlen(name))+1),name);
s->next=lt->sym[hv];
lt->sym[hv]=s;
return(s);
}


static struct lxt2_wr_symbol *lxt2_wr_symfind(struct lxt2_wr_trace *lt, const char *s)
{
int hv;
struct lxt2_wr_symbol *temp;

hv=lxt2_wr_hash(s);
if(!(temp=lt->sym[hv])) return(NULL); /* no hash entry, add here wanted to add */

while(temp)
        {
        if(!strcmp(temp->name,s))
                {
                return(temp); /* in table already */
                }
        if(!temp->next) break;
        temp=temp->next;
        }

return(NULL); /* not found, add here if you want to add*/
}


/*
 * compress facs to a prefix count + string + 0x00
 */
static void lxt2_wr_compress_fac(struct lxt2_wr_trace *lt, char *str)
{
int i;
int len = strlen(str);
int minlen = (len<lt->compress_fac_len) ? len : lt->compress_fac_len;

if(minlen>65535) minlen=65535;    /* keep in printable range--most hierarchies won't be this big anyway */

if(lt->compress_fac_str)
        {
        for(i=0;i<minlen;i++)
                {
                if(lt->compress_fac_str[i]!=str[i]) break;
                }
	lxt2_wr_emit_u16z(lt, i);
	lxt2_wr_emit_stringz(lt, str+i);
        free(lt->compress_fac_str);
        }
        else
        {
	lxt2_wr_emit_u16z(lt, 0);
	lxt2_wr_emit_stringz(lt, str);
        }

lt->compress_fac_str = (char *) malloc((lt->compress_fac_len=len)+1);
strcpy(lt->compress_fac_str, str);
}


/*
 * emit facs in sorted order along with geometry
 * and sync table info
 */

static void strip_brack(struct lxt2_wr_symbol *s)
{
char *lastch = s->name+s->namlen - 1;
if(*lastch!=']') return;
if(s->namlen<3) return;
lastch--;
while(lastch!=s->name)
	{
        if(*lastch=='.')
                {
                return; /* MTI SV [0.3] notation for implicit vars */
                }

	if(*lastch=='[')
		{
		*lastch=0x00;
		return;
		}
	lastch--;
	}
return;
}


static void lxt2_wr_emitfacs(struct lxt2_wr_trace *lt)
{
unsigned int i;

if((lt)&&(lt->numfacs))
	{
	struct lxt2_wr_symbol *s = lt->symchain;
	struct lxt2_wr_symbol **aliascache = (lxt2_wr_symbol**)calloc(lt->numalias ? lt->numalias : 1, sizeof(struct lxt2_wr_symbol *));
	unsigned int aliases_encountered, facs_encountered;

	lt->sorted_facs = (struct lxt2_wr_symbol **)calloc(lt->numfacs, sizeof(struct lxt2_wr_symbol *));

	if(lt->sorted_facs && aliascache)
		{
		if(lt->do_strip_brackets)
		for(i=0;i<lt->numfacs;i++)
			{
			lt->sorted_facs[lt->numfacs - i - 1] = s;	/* facs were chained backwards so reverse to restore bitslicing */
			strip_brack(s);
			s=s->symchain;
			}
		else
		for(i=0;i<lt->numfacs;i++)
			{
			lt->sorted_facs[lt->numfacs - i - 1] = s;	/* facs were chained backwards so reverse to restore bitslicing */
			s=s->symchain;
			}
		wave_msort(lt->sorted_facs, lt->numfacs);

		if(lt->partial_preference)
			{
			/* move preferenced facs up */
			struct lxt2_wr_symbol **prefcache = aliascache;
			int prefs_encountered = 0;

			facs_encountered = 0;
			for(i=0;i<lt->numfacs;i++)
				{
				if((lt->sorted_facs[i]->partial_preference)==0)
					{
					lt->sorted_facs[facs_encountered] = lt->sorted_facs[i];
					facs_encountered++;
					}
					else
					{
					prefcache[prefs_encountered] = lt->sorted_facs[i];
					prefs_encountered++;
					}
				}
			/* then append the non-preferenced facs */
			for(i=0;i<facs_encountered;i++)
				{
				prefcache[prefs_encountered+i] = lt->sorted_facs[i];
				}

			/* now make prefcache the main cache */
			aliascache = lt->sorted_facs;
			lt->sorted_facs = prefcache;
			}

		/* move facs up */
		aliases_encountered = 0, facs_encountered = 0;
		for(i=0;i<lt->numfacs;i++)
			{
			if((lt->sorted_facs[i]->flags&LXT2_WR_SYM_F_ALIAS)==0)
				{
				lt->sorted_facs[facs_encountered] = lt->sorted_facs[i];
				facs_encountered++;
				}
				else
				{
				aliascache[aliases_encountered] = lt->sorted_facs[i];
				aliases_encountered++;
				}
			}
		/* then append the aliases */
		for(i=0;i<aliases_encountered;i++)
			{
			lt->sorted_facs[facs_encountered+i] = aliascache[i];
			}


		for(i=0;i<lt->numfacs;i++)
			{
			lt->sorted_facs[i]->facnum = i;
			}

                if(!lt->timezero)
                        {
                        lxt2_wr_emit_u32(lt, lt->numfacs);       /* uncompressed */
                        }
                        else
                        {
                        lxt2_wr_emit_u32(lt, 0);                 /* uncompressed, flag to insert extra parameters */
                        lxt2_wr_emit_u32(lt, 8);                 /* uncompressed 8 counts timezero and on */
                        lxt2_wr_emit_u32(lt, lt->numfacs);       /* uncompressed */
                        lxt2_wr_emit_u64(lt, (lt->timezero >> 32) & 0xffffffffL, lt->timezero & 0xffffffffL); /* uncompressed */
                        }


		lxt2_wr_emit_u32(lt, lt->numfacbytes);	/* uncompressed */
		lxt2_wr_emit_u32(lt, lt->longestname);	/* uncompressed */

		lt->facname_offset=lt->position;

		lxt2_wr_emit_u32(lt, 0); 		/* uncompressed : placeholder for zfacnamesize     */
		lxt2_wr_emit_u32(lt, 0);		/* uncompressed : placeholder for zfacname_predec_size */
		lxt2_wr_emit_u32(lt, 0); 		/* uncompressed : placeholder for zfacgeometrysize */
		lxt2_wr_emit_u8(lt, lt->timescale);	/* timescale (-9 default == nsec) */

		fflush(lt->handle);
		lt->zfacname_size = lt->position;
		lt->zhandle = gzdopen(dup(fileno(lt->handle)), "wb9");

		lt->zpackcount = 0;
		for(i=0;i<lt->numfacs;i++)
			{
		 	lxt2_wr_compress_fac(lt, lt->sorted_facs[i]->name);
			free(lt->sorted_facs[i]->name);
			lt->sorted_facs[i]->name = NULL;
			}
		free(lt->compress_fac_str); lt->compress_fac_str=NULL;
		lt->compress_fac_len=0;
		lt->zfacname_predec_size = lt->zpackcount;

		gzflush_buffered(lt, 1);
		fseeko(lt->handle, 0L, SEEK_END);
		lt->position=ftello(lt->handle);
		lt->zfacname_size = lt->position - lt->zfacname_size;

		lt->zhandle = gzdopen(dup(fileno(lt->handle)), "wb9");

		lt->facgeometry_offset = lt->position;
		for(i=0;i<lt->numfacs;i++)
			{
			if((lt->sorted_facs[i]->flags&LXT2_WR_SYM_F_ALIAS)==0)
				{
				lxt2_wr_emit_u32z(lt, lt->sorted_facs[i]->rows);
				lxt2_wr_emit_u32z(lt, lt->sorted_facs[i]->msb);
				lxt2_wr_emit_u32z(lt, lt->sorted_facs[i]->lsb);
				lxt2_wr_emit_u32z(lt, lt->sorted_facs[i]->flags);
				}
				else
				{
				lxt2_wr_emit_u32z(lt, lt->sorted_facs[i]->aliased_to->facnum);
				lxt2_wr_emit_u32z(lt, lt->sorted_facs[i]->msb);
				lxt2_wr_emit_u32z(lt, lt->sorted_facs[i]->lsb);
				lxt2_wr_emit_u32z(lt, LXT2_WR_SYM_F_ALIAS);
				}
			}

		gzflush_buffered(lt, 1);
		fseeko(lt->handle, 0L, SEEK_END);
		lt->position=ftello(lt->handle);
		lt->break_header_size = lt->position;			/* in case we need to emit multiple lxt2s with same header */
		lt->zfacgeometry_size = lt->position - lt->facgeometry_offset;

		fseeko(lt->handle, lt->facname_offset, SEEK_SET);
		lxt2_wr_emit_u32(lt, lt->zfacname_size);		/* backpatch sizes... */
		lxt2_wr_emit_u32(lt, lt->zfacname_predec_size);
		lxt2_wr_emit_u32(lt, lt->zfacgeometry_size);

		lt->numfacs = facs_encountered;				/* don't process alias value changes ever */
		}

	free(aliascache);
	}
}


/*
 * initialize the trace and get back an lt context
 */
struct lxt2_wr_trace *lxt2_wr_init(const char *name)
{
struct lxt2_wr_trace *lt=(struct lxt2_wr_trace *)calloc(1, sizeof(struct lxt2_wr_trace));

if((!name)||(!(lt->handle=fopen(name, "wb"))))
	{
	free(lt);
	lt=NULL;
	}
	else
	{
	lt->lxtname = strdup(name);

	lxt2_wr_emit_u16(lt, LXT2_WR_HDRID);
	lxt2_wr_emit_u16(lt, LXT2_WR_VERSION);
	lxt2_wr_emit_u8 (lt, LXT2_WR_GRANULE_SIZE);	/* currently 32 or 64 */
	lt->timescale = -9;
	lt->maxgranule = LXT2_WR_GRANULE_NUM;
	lxt2_wr_set_compression_depth(lt, 4);	/* set fast/loose compression depth, user can fix this any time after init */
	lt->initial_value = 'x';
	}

return(lt);
}


/*
 * setting break size
 */
void lxt2_wr_set_break_size(struct lxt2_wr_trace *lt, off_t siz)
{
if(lt)
	{
	lt->break_size = siz;
	}
}


/*
 * enable/disable partial dump mode (for faster reads)
 */
void lxt2_wr_set_partial_off(struct lxt2_wr_trace *lt)
{
if(lt)
	{
	lt->partial = 0;
	lt->partial_zip = 0;
	}
}

void lxt2_wr_set_partial_on(struct lxt2_wr_trace *lt, int zipmode)
{
if(lt)
	{
	lt->partial = 1;
	lt->partial_zip = (zipmode != 0);
	lt->partial_iter = LXT2_WR_PARTIAL_SIZE;
	}
}

void lxt2_wr_set_partial_preference(struct lxt2_wr_trace *lt, const char *name)
{
struct lxt2_wr_symbol *s;

if((lt)&&(name)&&(!lt->sorted_facs))
	{
	s=lxt2_wr_symfind(lt, name);
	if(s)
		{
		while(s->aliased_to)    /* find root alias */
		        {
		        s=s->aliased_to;
		        }

		s->partial_preference = 1;
		}
	}
}


/*
 * enable/disable checkpointing (for smaller files)
 */
void lxt2_wr_set_checkpoint_off(struct lxt2_wr_trace *lt)
{
if(lt)
	{
	lt->no_checkpoint = 1;
	}
}

void lxt2_wr_set_checkpoint_on(struct lxt2_wr_trace *lt)
{
if(lt)
	{
	lt->no_checkpoint = 0;
	}
}


/*
 * set initial value of trace (0, 1, x, z) only legal vals
 */
void lxt2_wr_set_initial_value(struct lxt2_wr_trace *lt, char value)
{
if(lt)
	{
	switch(value)
		{
		case '0':
		case '1':
		case 'x':
		case 'z':	break;
		case 'Z':	value = 'z'; break;
		default:	value = 'x'; break;
		}

	lt->initial_value = value;
	}
}


/*
 * maint function for finding a symbol if it exists
 */
struct lxt2_wr_symbol *lxt2_wr_symbol_find(struct lxt2_wr_trace *lt, const char *name)
{
struct lxt2_wr_symbol *s=NULL;

if((lt)&&(name)) s=lxt2_wr_symfind(lt, name);
return(s);
}


/*
 * add a trace (if it doesn't exist already)
 */
struct lxt2_wr_symbol *lxt2_wr_symbol_add(struct lxt2_wr_trace *lt, const char *name, unsigned int rows, int msb, int lsb, int flags)
{
struct lxt2_wr_symbol *s;
int len;
int flagcnt;

if((!lt)||(lt->sorted_facs)) return(NULL);

flagcnt = ((flags&LXT2_WR_SYM_F_INTEGER)!=0) + ((flags&LXT2_WR_SYM_F_DOUBLE)!=0) + ((flags&LXT2_WR_SYM_F_STRING)!=0);

if((flagcnt>1)||(!lt)||(!name)||(lxt2_wr_symfind(lt, name))) return (NULL);

s=lxt2_wr_symadd(lt, name, lxt2_wr_hash(name));
s->rows = rows;
s->flags = flags&(~LXT2_WR_SYM_F_ALIAS);	/* aliasing makes no sense here.. */

if(!flagcnt)
	{
	s->msb = msb;
	s->lsb = lsb;
	s->len = (msb<lsb) ? (lsb-msb+1) : (msb-lsb+1);
	}

if(flags&LXT2_WR_SYM_F_DOUBLE)
	{
	s->value = strdup("NaN");
	}
	else
	{
	if(flags & LXT2_WR_SYM_F_INTEGER)
		{
		s->len = 32;
		}

	s->value = (char*)malloc(s->len + 1);
	memset(s->value, lt->initial_value, s->len);
	s->value[s->len]=0;

	s->msk = LXT2_WR_GRAN_1VAL; /* stuff in an initial value */
	switch(lt->initial_value)
		{
		case '0':	s->chg[0] = LXT2_WR_ENC_0; break;
		case '1':	s->chg[0] = LXT2_WR_ENC_1; break;
		case 'z':	s->chg[0] = LXT2_WR_ENC_Z; break;
		default:	s->chg[0] = LXT2_WR_ENC_X; break;
		}
        s->chgpos++;		/* don't worry that a time doesn't exist as it will soon enough.. */
	}

s->symchain = lt->symchain;
lt->symchain = s;

lt->numfacs++;

if((len=strlen(name)) > lt->longestname) lt->longestname = len;
lt->numfacbytes += (len+1);

return(s);
}

/*
 * add an alias trace (if it doesn't exist already and orig is found)
 */
struct lxt2_wr_symbol *lxt2_wr_symbol_alias(struct lxt2_wr_trace *lt, const char *existing_name, const char *alias, int msb, int lsb)
{
struct lxt2_wr_symbol *s, *sa;
int len;
int bitlen;
int flagcnt;

if((!lt)||(!existing_name)||(!alias)||(!(s=lxt2_wr_symfind(lt, existing_name)))||(lxt2_wr_symfind(lt, alias))) return (NULL);

if(lt->sorted_facs) return(NULL);

while(s->aliased_to)	/* find root alias */
	{
	s=s->aliased_to;
	}

flagcnt = ((s->flags&LXT2_WR_SYM_F_INTEGER)!=0) + ((s->flags&LXT2_WR_SYM_F_DOUBLE)!=0) + ((s->flags&LXT2_WR_SYM_F_STRING)!=0);
bitlen = (msb<lsb) ? (lsb-msb+1) : (msb-lsb+1);
if((!flagcnt)&&(bitlen!=s->len)) return(NULL);

sa=lxt2_wr_symadd(lt, alias, lxt2_wr_hash(alias));
sa->flags = LXT2_WR_SYM_F_ALIAS;	/* only point this can get set */
sa->aliased_to = s;

if(!flagcnt)
	{
	sa->msb = msb;
	sa->lsb = lsb;
	sa->len = bitlen;
	}

sa->symchain = lt->symchain;
lt->symchain = sa;
lt->numfacs++;
lt->numalias++;
if((len=strlen(alias)) > lt->longestname) lt->longestname = len;
lt->numfacbytes += (len+1);

return(sa);
}


/*
 * set current time/granule updating
 */
int lxt2_wr_inc_time_by_delta(struct lxt2_wr_trace *lt, unsigned int timeval)
{
return(lxt2_wr_set_time64(lt, lt->maxtime + (lxttime_t)timeval));
}

int lxt2_wr_set_time(struct lxt2_wr_trace *lt, unsigned int timeval)
{
return(lxt2_wr_set_time64(lt, (lxttime_t)timeval));
}

int lxt2_wr_inc_time_by_delta64(struct lxt2_wr_trace *lt, lxttime_t timeval)
{
return(lxt2_wr_set_time64(lt, lt->maxtime + timeval));
}


/*
 * file size limiting/header cloning...
 */
static void lxt2_wr_emit_do_breakfile(struct lxt2_wr_trace *lt)
{
unsigned int len = strlen(lt->lxtname);
int i;
char *tname = (char*)malloc(len + 30);
FILE *f2, *clone;
off_t cnt, seg;
char buf[32768];

for(i=len;i>0;i--)
	{
	if(lt->lxtname[i]=='.') break;
	}

if(!i)
	{
	sprintf(tname, "%s_%03u.lxt", lt->lxtname, ++lt->break_number);
	}
	else
	{
	memcpy(tname, lt->lxtname, i);
	sprintf(tname+i, "_%03u.lxt", ++lt->break_number);
	}

f2 = fopen(tname, "wb");
if(!f2)	/* if error, keep writing to same output file...sorry */
	{
	free(tname);
	return;
	}

clone = fopen(lt->lxtname, "rb");
if(!clone)
	{ /* this should never happen */
	fclose(f2);
	unlink(tname);
	free(tname);
	return;
	}

/* clone original header */
for(cnt = 0; cnt < lt->break_header_size; cnt += sizeof(buf))
	{
	seg = lt->break_header_size - cnt;
	if(seg > (off_t)sizeof(buf))
		{
		seg = sizeof(buf);
		}

	if(fread(buf, seg, 1, clone))
		{
		if(!fwrite(buf, seg, 1, f2)) break; /* write error! */
		}
	}

fclose(clone);
fclose(lt->handle);
lt->handle = f2;
free(tname);
}


/*
 * emit granule
 */
void lxt2_wr_flush_granule(struct lxt2_wr_trace *lt, int do_finalize)
{
unsigned int idx_nbytes, map_nbytes, i, j;
struct lxt2_wr_symbol *s;
unsigned int partial_iter;
unsigned int iter, iter_hi;
unsigned char using_partial, using_partial_zip=0;
off_t current_iter_pos=0;
int early_flush;

if(lt->flush_valid)
	{
	if(lt->flushtime == lt->lasttime)
		{
		return;
		}

	lt->flush_valid = 0;
	}

lt->granule_dirty = 0;

if((using_partial=(lt->partial)&&(lt->numfacs>lt->partial_iter)))
	{
	partial_iter = lt->partial_iter;
	using_partial_zip = lt->partial_zip;
	}
	else
	{
	partial_iter = lt->numfacs;
	}

if(!lt->timegranule)
	{
	int attempt_break_state = 2;

	do	{
		fseeko(lt->handle, 0L, SEEK_END);
		lt->current_chunk=lt->position = ftello(lt->handle);

		if((lt->break_size)&&(attempt_break_state==2)&&(lt->position >= lt->break_size)&&(lt->position != lt->break_header_size))
			{
			lxt2_wr_emit_do_breakfile(lt);
			attempt_break_state--;
			}
			else
			{
			attempt_break_state = 0;
			}
		} while(attempt_break_state);

	/* fprintf(stderr, "First chunk position is %d (0x%08x)\n", lt->current_chunk, lt->current_chunk); */
	lxt2_wr_emit_u32(lt, 0);	/* size of this section (uncompressed) */
	lxt2_wr_emit_u32(lt, 0);	/* size of this section (compressed)   */
	lxt2_wr_emit_u64(lt, 0, 0);	/* begin time of section               */
	lxt2_wr_emit_u64(lt, 0, 0);	/* end time of section                 */
	fflush(lt->handle);
	lt->current_chunkz = lt->position;
	/* fprintf(stderr, "First chunkz position is %d (0x%08x)\n", lt->current_chunkz, lt->current_chunkz); */

	if(!using_partial_zip)
		{
		lt->zhandle = gzdopen(dup(fileno(lt->handle)), lt->zmode);
		}
		else
		{
		lt->zpackcount_cumulative = 0;
		}
	lt->zpackcount = 0;
	}



for(iter=0; iter<lt->numfacs; iter=iter_hi)
{
unsigned int total_chgs;
unsigned int partial_length;

total_chgs = 0;
/* partial_length = 0; */ /* scan-build : never read */

iter_hi = iter + partial_iter;
if(iter_hi > lt->numfacs) iter_hi = lt->numfacs;

for(j=iter;j<iter_hi;j++)
	{
	granmsk_t msk = lt->sorted_facs[j]->msk;

	lt->mapdict = lxt2_wr_ds_splay (msk, lt->mapdict);
	if((!lt->mapdict)||(lt->mapdict->item != msk))
		{
		lt->mapdict = lxt2_wr_ds_insert(msk, lt->mapdict, lt->num_map_entries);
		lt->num_map_entries++;

		if(lt->mapdict_curr)
			{
			lt->mapdict_curr->next = lt->mapdict;
			lt->mapdict_curr = lt->mapdict;
			}
			else
			{
			lt->mapdict_head =  lt->mapdict_curr = lt->mapdict;
			}
		}
	}

if(lt->num_map_entries <= 256) { map_nbytes = 1; }
else if(lt->num_map_entries <= 256*256) { map_nbytes = 2; }
else if(lt->num_map_entries <= 256*256*256) { map_nbytes = 3; }
else { map_nbytes = 4; }

if((lt->num_dict_entries+LXT2_WR_DICT_START) <= 256) { idx_nbytes = 1; }
else if((lt->num_dict_entries+LXT2_WR_DICT_START) <= 256*256) { idx_nbytes = 2; }
else if((lt->num_dict_entries+LXT2_WR_DICT_START) <= 256*256*256) { idx_nbytes = 3; }
else { idx_nbytes = 4; }

if(using_partial)
	{
	/* skip */
	partial_length = 1 +			/* lt->timepos */
	lt->timepos * sizeof(lxttime_t)+	/* timevals */

	1 +					/* map_nbytes */
	(iter_hi-iter) * map_nbytes +		/* actual map */
	1;					/* idx_nbytes */

	for(j=iter;j<iter_hi;j++)
		{
	        s=lt->sorted_facs[j];
		total_chgs += s->chgpos;
		}
	total_chgs *= idx_nbytes;		/* vch skip */

	partial_length += total_chgs; 		/* actual changes */

	if(using_partial_zip)
		{
		fseeko(lt->handle, 0L, SEEK_END);
		current_iter_pos = ftello(lt->handle);
		lxt2_wr_emit_u32(lt, 0);		/* size of this section (compressed)   */
		lxt2_wr_emit_u32(lt, partial_length+9);	/* size of this section (uncompressed) */
		lxt2_wr_emit_u32(lt, iter);		/* begin iter of section               */
		fflush(lt->handle);

		lt->zhandle = gzdopen(dup(fileno(lt->handle)), lt->zmode);
		lt->zpackcount = 0;
		}

	lxt2_wr_emit_u8z(lt, LXT2_WR_GRAN_SECT_TIME_PARTIAL);
	lxt2_wr_emit_u32z(lt, iter);
	lxt2_wr_emit_u32z(lt, partial_length);
	}
	else
	{
	lxt2_wr_emit_u8z(lt, LXT2_WR_GRAN_SECT_TIME);
	}

lxt2_wr_emit_u8z(lt, lt->timepos);
for(i=0;i<lt->timepos;i++)
	{
	lxt2_wr_emit_u64z(lt, (lt->timetable[i]>>32)&0xffffffff, lt->timetable[i]&0xffffffff);
	}
gzflush_buffered(lt, 0);


lxt2_wr_emit_u8z(lt, map_nbytes);
for(j=iter;j<iter_hi;j++)
	{
	unsigned int val;
        s=lt->sorted_facs[j];
	lt->mapdict = lxt2_wr_ds_splay (s->msk, lt->mapdict);
	val = lt->mapdict->val;

	switch(map_nbytes)
		{
		case 1:	lxt2_wr_emit_u8z(lt, val); break;
		case 2: lxt2_wr_emit_u16z(lt, val); break;
		case 3: lxt2_wr_emit_u24z(lt, val); break;
		case 4: lxt2_wr_emit_u32z(lt, val); break;
		}

	s->msk = LXT2_WR_GRAN_0VAL;
	}


lxt2_wr_emit_u8z(lt, idx_nbytes);
gzflush_buffered(lt, 0);
for(j=iter;j<iter_hi;j++)
	{
        s=lt->sorted_facs[j];

	for(i=0;i<s->chgpos;i++)
		{
		switch(idx_nbytes)
			{
			case 1:	lxt2_wr_emit_u8z (lt, s->chg[i]); break;
			case 2: lxt2_wr_emit_u16z(lt, s->chg[i]); break;
			case 3: lxt2_wr_emit_u24z(lt, s->chg[i]); break;
			case 4: lxt2_wr_emit_u32z(lt, s->chg[i]); break;
			}
		}

	s->chgpos = 0;
	}

if(using_partial_zip)
	{
	off_t clen;

	gzflush_buffered(lt, 1);
	fseeko(lt->handle, 0L, SEEK_END);
	lt->position=ftello(lt->handle);

	clen = lt->position - current_iter_pos - 12;
	fseeko(lt->handle, current_iter_pos, SEEK_SET);

	lt->zpackcount_cumulative+=lt->zpackcount;

	lxt2_wr_emit_u32(lt, clen);
	}
	else
	{
	gzflush_buffered(lt, 0);
	}
} /* ...for(iter) */


lt->timepos = 0;
lt->timegranule++;

if(lt->break_size)
	{
	early_flush = (ftello(lt->handle) >= lt->break_size);
	}
	else
	{
	early_flush = 0;
	}

if((lt->timegranule>=lt->maxgranule)||(do_finalize)||(early_flush))
	{
	off_t unclen, clen;
	lxt2_wr_ds_Tree *dt, *dt2;
	lxt2_wr_dslxt_Tree *ds, *ds2;

	if(using_partial_zip)
		{
		fseeko(lt->handle, 0L, SEEK_END);
		current_iter_pos = ftello(lt->handle);
		lxt2_wr_emit_u32(lt, 0);		/* size of this section (compressed)   */
		lxt2_wr_emit_u32(lt, 0);		/* size of this section (uncompressed) */
		lxt2_wr_emit_u32(lt, ~0);		/* control section		       */
		fflush(lt->handle);

		lt->zhandle = gzdopen(dup(fileno(lt->handle)), lt->zmode);
		lt->zpackcount = 0;
		}

	/* fprintf(stderr, "reached granule %d, finalizing block for section %d\n", lt->timegranule, lt->numsections); */
	lt->numsections++;

	/* finalize string dictionary */
	lxt2_wr_emit_u8z(lt, LXT2_WR_GRAN_SECT_DICT);

	ds = lt->dict_head;
	/* fprintf(stderr, "num_dict_entries: %d\n", lt->num_dict_entries); */
	gzflush_buffered(lt, 0);
	for(i=0;i<lt->num_dict_entries;i++)
		{
		/* fprintf(stderr, "%8d %8d) '%s'\n", ds->val, i, ds->item); */
		if(ds->val != i)
			{
			fprintf(stderr, "internal error line %d\n", __LINE__);
			exit(255);
			}

		lxt2_wr_emit_stringz(lt, ds->item);
		ds2 = ds->next;
		free(ds->item);
		free(ds);
		ds = ds2;
		}
	lt->dict_head = lt->dict_curr = lt->dict = NULL;

	/* finalize map dictionary */
	dt = lt->mapdict_head;
	/* fprintf(stderr, "num_map_entries: %d\n", lt->num_map_entries); */
	gzflush_buffered(lt, 0);
	for(i=0;i<lt->num_map_entries;i++)
		{
		/* fprintf(stderr, "+++ %08x (%d)(%d)\n", dt->item, i, dt->val); */
		if(((unsigned int)dt->val) != i)
			{
			fprintf(stderr, "internal error line %d\n", __LINE__);
			exit(255);
			}

#if LXT2_WR_GRANULE_SIZE > 32
		lxt2_wr_emit_u64z(lt, (dt->item>>32)&0xffffffff, dt->item&0xffffffff);
#else
		lxt2_wr_emit_u32z(lt, dt->item);
#endif

		dt2 = dt->next;
		free(dt);
		dt = dt2;
		}
	lt->mapdict_head = lt->mapdict_curr = lt->mapdict = NULL;

	lxt2_wr_emit_u32z(lt, lt->num_dict_entries);		/* -12 */
	lxt2_wr_emit_u32z(lt, lt->dict_string_mem_required);	/* -8 */
	lxt2_wr_emit_u32z(lt, lt->num_map_entries);		/* -4 */

	lt->num_map_entries = 0;
	lt->num_dict_entries = lt->dict_string_mem_required = 0;

	/* fprintf(stderr, "returned from finalize..\n"); */

	if(using_partial_zip)
		{
		off_t c_len;

		gzflush_buffered(lt, 1);
		fseeko(lt->handle, 0L, SEEK_END);
		lt->position=ftello(lt->handle);

		c_len = lt->position - current_iter_pos - 12;
		fseeko(lt->handle, current_iter_pos, SEEK_SET);

		lt->zpackcount_cumulative+=lt->zpackcount;
		lxt2_wr_emit_u32(lt, c_len);
		lxt2_wr_emit_u32(lt, lt->zpackcount);
		}
		else
		{
		gzflush_buffered(lt, 1);
		}

        fseeko(lt->handle, 0L, SEEK_END);
        lt->position=ftello(lt->handle);
	/* fprintf(stderr, "file position after dumping dict: %d 0x%08x\n", lt->position, lt->position); */

	unclen = lt->zpackcount;
	clen = lt->position - lt->current_chunkz;

	/* fprintf(stderr, "%d/%d un/compressed bytes in section\n", unclen, clen); */

	fseeko(lt->handle, lt->current_chunk, SEEK_SET);
	if(using_partial_zip)
		{
		lxt2_wr_emit_u32(lt, lt->zpackcount_cumulative);
		lxt2_wr_emit_u32(lt, clen);
		}
		else
		{
		lxt2_wr_emit_u32(lt, unclen);
		lxt2_wr_emit_u32(lt, clen);
		}
	lxt2_wr_emit_u64(lt, (lt->firsttime>>32)&0xffffffff, lt->firsttime&0xffffffff);
	lxt2_wr_emit_u64(lt, (lt->lasttime>>32)&0xffffffff, lt->lasttime&0xffffffff);

	/* fprintf(stderr, "start: %lld, end %lld\n", lt->firsttime, lt->lasttime); */

	lt->timegranule=0;
	lt->numblock++;
	}

if(do_finalize)
	{
	lt->flush_valid = 1;
	lt->flushtime = lt->lasttime;
	}
}


int lxt2_wr_set_time64(struct lxt2_wr_trace *lt, lxttime_t timeval)
{
int rc=0;

if(lt)
	{
	if(lt->timeset)
		{
		if(timeval > lt->maxtime)
			{
			if(lt->bumptime)
				{
				lt->bumptime = 0;

				if(!lt->flush_valid)
					{
					lt->timepos++;
					}
					else
					{
					lt->flush_valid = 0;
					}

				if(lt->timepos == LXT2_WR_GRANULE_SIZE)
					{
					/* fprintf(stderr, "flushing granule to disk at time %d\n", (unsigned int)timeval); */
					lxt2_wr_flush_granule(lt, 0);
					}
				}

			/* fprintf(stderr, "updating time to %d (%d dict entries/%d bytes)\n", (unsigned int)timeval, lt->num_dict_entries, lt->dict_string_mem_required); */
			lt->timetable[lt->timepos] = timeval;
			lt->lasttime = timeval;
			}
		}
		else
		{
		lt->timeset = 1;
		lt->mintime = lt->maxtime = timeval;

		lt->timetable[lt->timepos] = timeval;
		}

	if( (!lt->timepos) && (!lt->timegranule) )
		{
		lt->firsttime = timeval;
		lt->lasttime = timeval;
		}

	if( (!lt->timepos) && (!lt->timegranule) && ((!lt->numblock)||(!lt->no_checkpoint)) )
	        {
		/* fprintf(stderr, "initial value burst timepos==0, timegranule==0\n"); */
		if(lt->blackout)
			{
			lt->blackout = 0;
			lxt2_wr_set_dumpoff(lt);
			}
		else
			{
			struct lxt2_wr_symbol *s = lt->symchain;
		        while(s)
		                {
		                if((!(s->flags&LXT2_WR_SYM_F_ALIAS))&&(s->rows<2))
		                        {
					if(!(s->flags&(LXT2_WR_SYM_F_DOUBLE|LXT2_WR_SYM_F_STRING)))
						{
			                        lxt2_wr_emit_value_bit_string(lt, s, 0, s->value);
						}
					else if (s->flags&LXT2_WR_SYM_F_DOUBLE)
						{
						double value = 0;

						sscanf(s->value, "%lg", &value);
						errno = 0;
						lxt2_wr_emit_value_double(lt, s, 0, value);
						}
					else if (s->flags&LXT2_WR_SYM_F_STRING)
						{
						lxt2_wr_emit_value_string(lt, s, 0, s->value);
						}
		                        }
		                s=s->symchain;
		                }
			}
		/* fprintf(stderr, "done initial value burst timepos==0, timegranule==0\n"); */
	        }

	lt->granule_dirty = 1;
	rc = 1;
	}

return(rc);
}


/*
 * sets trace timescale as 10**x seconds
 */
void lxt2_wr_set_timescale(struct lxt2_wr_trace *lt, int timescale)
{
if(lt)
	{
	lt->timescale = timescale;
	}
}


/*
 * set number of granules per section
 * (can modify dynamically)
 */
void lxt2_wr_set_maxgranule(struct lxt2_wr_trace *lt, unsigned int maxgranule)
{
if(lt)
	{
	if(!maxgranule) maxgranule = ~0;
	lt->maxgranule = maxgranule;
	}
}


/*
 * Sets bracket stripping (useful for VCD conversions of
 * bitblasted nets)
 */
void lxt2_wr_symbol_bracket_stripping(struct lxt2_wr_trace *lt, int doit)
{
if(lt)
	{
	lt->do_strip_brackets = (doit!=0);
	}
}



static char *lxt2_wr_expand_integer_to_bits(unsigned int len, int value)
{
static char s[33];
char *p = s;
unsigned int i;

if(len>32) len=32;

len--;

for(i=0;i<=len;i++)
	{
	*(p++) = '0' | ((value & (1<<(len-i)))!=0);
	}
*p = 0;

return(s);
}


int lxt2_wr_emit_value_int(struct lxt2_wr_trace *lt, struct lxt2_wr_symbol *s, unsigned int row, int value)
{
int rc=0;

if((!lt)||(lt->blackout)||(!s)||(row)) return(rc);

return(lxt2_wr_emit_value_bit_string(lt, s, row, lxt2_wr_expand_integer_to_bits(s->len, value)));
}



int lxt2_wr_emit_value_double(struct lxt2_wr_trace *lt, struct lxt2_wr_symbol *s, unsigned int row, double value)
{
int rc=0;

if((!lt)||(lt->blackout)||(!s)||(row)) return(rc);

if(!lt->emitted)
	{
	lxt2_wr_emitfacs(lt);
	lt->emitted = 1;

	if(!lt->timeset)
		{
		lxt2_wr_set_time(lt, 0);
		}
	}

while(s->aliased_to)	/* find root alias if exists */
	{
	s=s->aliased_to;
	}

if(s->flags&LXT2_WR_SYM_F_DOUBLE)
	{
	char d_buf[32];
	unsigned int idx;

	rc = 1;
	sprintf(d_buf, "%.16g", value);
	if(!strcmp(d_buf, s->value)) return(rc);

	lt->bumptime = 1;
	free(s->value);
	s->value = strdup(d_buf);

	lt->dict = lxt2_wr_dslxt_splay (s->value, lt->dict);

	if(!lxt2_wr_dslxt_success)
		{
		unsigned int vlen = strlen(d_buf)+1;
		char *vcopy = (char *)malloc(vlen);
		strcpy(vcopy, d_buf);
		lt->dict_string_mem_required += vlen;
		lt->dict = lxt2_wr_dslxt_insert(vcopy, lt->dict, lt->num_dict_entries);

		if(lt->dict_curr)
			{
			lt->dict_curr->next = lt->dict;
			lt->dict_curr = lt->dict;
			}
			else
			{
			lt->dict_head =  lt->dict_curr = lt->dict;
			}

		idx = lt->num_dict_entries + LXT2_WR_DICT_START;
		lt->num_dict_entries++;
		}
		else
		{
		idx = lt->dict->val + LXT2_WR_DICT_START;
		}

	if((s->msk & (LXT2_WR_GRAN_1VAL<<lt->timepos)) == LXT2_WR_GRAN_0VAL)
		{
		s->msk |= (LXT2_WR_GRAN_1VAL<<lt->timepos);
		s->chg[s->chgpos] = idx;

		s->chgpos++;
		}
		else
		{
		s->chg[s->chgpos-1] = idx;
		}

	lt->granule_dirty = 1;
	}

return(rc);
}


int lxt2_wr_emit_value_string(struct lxt2_wr_trace *lt, struct lxt2_wr_symbol *s, unsigned int row, char *value)
{
int rc=0;

if((!lt)||(lt->blackout)||(!s)||(!value)||(row)) return(rc);

if(!lt->emitted)
	{
	lxt2_wr_emitfacs(lt);
	lt->emitted = 1;

	if(!lt->timeset)
		{
		lxt2_wr_set_time(lt, 0);
		}
	}

while(s->aliased_to)	/* find root alias if exists */
	{
	s=s->aliased_to;
	}

if(s->flags&LXT2_WR_SYM_F_STRING)
	{
	unsigned int idx;

	rc = 1;
	if(!strcmp(value, s->value)) return(rc);

	lt->bumptime = 1;
	free(s->value);
	s->value = strdup(value);

	lt->dict = lxt2_wr_dslxt_splay (s->value, lt->dict);

	if(!lxt2_wr_dslxt_success)
		{
		unsigned int vlen = strlen(value)+1;
		char *vcopy = (char *)malloc(vlen);
		strcpy(vcopy, value);
		lt->dict_string_mem_required += vlen;
		lt->dict = lxt2_wr_dslxt_insert(vcopy, lt->dict, lt->num_dict_entries);

		if(lt->dict_curr)
			{
			lt->dict_curr->next = lt->dict;
			lt->dict_curr = lt->dict;
			}
			else
			{
			lt->dict_head =  lt->dict_curr = lt->dict;
			}

		idx = lt->num_dict_entries + LXT2_WR_DICT_START;
		lt->num_dict_entries++;
		}
		else
		{
		idx = lt->dict->val + LXT2_WR_DICT_START;
		}

	if((s->msk & (LXT2_WR_GRAN_1VAL<<lt->timepos)) == LXT2_WR_GRAN_0VAL)
		{
		s->msk |= (LXT2_WR_GRAN_1VAL<<lt->timepos);
		s->chg[s->chgpos] = idx;

		s->chgpos++;
		}
		else
		{
		s->chg[s->chgpos-1] = idx;
		}

	lt->granule_dirty = 1;
	}

return(rc);
}


int lxt2_wr_emit_value_bit_string(struct lxt2_wr_trace *lt, struct lxt2_wr_symbol *s, unsigned int row, char *value)
{
int rc=0;
char *vpnt;
char *vfix;
int valuelen;
int i;

if((!lt)||(lt->blackout)||(!s)||(!value)||(!*value)||(row)) return(rc);

if(!lt->emitted)
	{
	lxt2_wr_emitfacs(lt);
	lt->emitted = 1;

	if(!lt->timeset)
		{
		lxt2_wr_set_time(lt, 0);
		}
	}

while(s->aliased_to)	/* find root alias if exists */
	{
	s=s->aliased_to;
	}

valuelen = strlen(value);	/* ensure string is proper length */
if(valuelen == s->len)
	{
	vfix = (char*)wave_alloca(s->len+1);
	strcpy(vfix, value);
	value = vfix;
	}
	else
	{
	vfix = (char*)wave_alloca(s->len+1);

	if(valuelen < s->len)
		{
		int lendelta = s->len - valuelen;
		memset(vfix, (value[0]!='1') ? value[0] : '0', lendelta);
		strcpy(vfix+lendelta, value);
		}
		else
		{
		memcpy(vfix, value, s->len);
		vfix[s->len] = 0;
		}

	value = vfix;
	}

for(i=0;i<s->len;i++)
	{
	unsigned char ch = value[i];
	if((ch>='A')&&(ch<='Z')) value[i] = ch + ('a'-'A');
	}

if ( (lt->timepos || lt->timegranule) && !strcmp(value, s->value) )
	{
	return(1);	/* redundant value change */
	}


if(!(s->flags&(LXT2_WR_SYM_F_DOUBLE|LXT2_WR_SYM_F_STRING)))
	{
	char prevch;
	int idx;

	lt->bumptime = 1;

	vpnt = value;
	prevch = *vpnt;
	while(*vpnt)
		{
		if(prevch == *vpnt)
			{
			vpnt++;
			}
			else
			{
			prevch = 0;
			break;
			}
		}

	switch(prevch)
		{
		case '0':	idx = LXT2_WR_ENC_0; break;
		case '1':	idx = LXT2_WR_ENC_1; break;
		case 'X':
		case 'x':	idx = LXT2_WR_ENC_X; break;
		case 'Z':
		case 'z':	idx = LXT2_WR_ENC_Z; break;
		default:	idx = -1; break;
		}

	if((lt->timepos)||(lt->timegranule))
		{
		for(i=0;i<s->len;i++)
			{
			char ch = value[i];

			switch(ch)
				{
				case '0': if(s->value[i]!='1') goto nextalg; else break;
				case '1': if(s->value[i]!='0') goto nextalg; else break;
				default:  goto nextalg;
				}
			}
		idx = LXT2_WR_ENC_INV; goto do_enc;

		nextalg:
		if(s->len > 1)
			{
			if(!memcmp(s->value+1, value, s->len-1))
				{
				if((value[s->len-1]&0xfe)=='0')
					{
					idx = LXT2_WR_ENC_LSH0 + (value[s->len-1]&0x01);
					goto do_enc;
					}
				}
			else
			if(!memcmp(s->value, value+1, s->len-1))
				{
				if((value[0]&0xfe)=='0')
					{
					idx = LXT2_WR_ENC_RSH0 + (value[0]&0x01);
					goto do_enc;
					}
				}

			if(s->len <= 32)
				{
				unsigned int intval_old = 0, intval_new = 0;
				unsigned int msk;

				for(i=0;i<s->len;i++)
					{
					char ch = value[i];
					if((ch!='0')&&(ch!='1')) goto idxchk;
					intval_new <<= 1;
					intval_new |= ((unsigned int)(ch&1));

					ch = s->value[i];
					if((ch!='0')&&(ch!='1')) goto idxchk;
					intval_old <<= 1;
					intval_old |= ((unsigned int)(ch&1));
					}

				msk = (~0)>>(32-s->len);
				if( ((intval_old+1)&msk) == intval_new ) { idx = LXT2_WR_ENC_ADD1; goto do_enc; }
				if( ((intval_old-1)&msk) == intval_new ) { idx = LXT2_WR_ENC_SUB1; goto do_enc; }

				if( ((intval_old+2)&msk) == intval_new ) { idx = LXT2_WR_ENC_ADD2; goto do_enc; }
				if( ((intval_old-2)&msk) == intval_new ) { idx = LXT2_WR_ENC_SUB2; goto do_enc; }

				if( ((intval_old+3)&msk) == intval_new ) { idx = LXT2_WR_ENC_ADD3; goto do_enc; }
				if( ((intval_old-3)&msk) == intval_new ) { idx = LXT2_WR_ENC_SUB3; goto do_enc; }

				if(s->len > 2)
					{
					if( ((intval_old+4)&msk) == intval_new ) { idx = LXT2_WR_ENC_ADD4; goto do_enc; }
					if( ((intval_old-4)&msk) == intval_new ) { idx = LXT2_WR_ENC_SUB4; goto do_enc; }
					}

				}
			}
		}


idxchk:	if(idx<0)
		{
		vpnt = lxt2_wr_vcd_truncate_bitvec(value);
		lt->dict = lxt2_wr_dslxt_splay (vpnt, lt->dict);

		if(!lxt2_wr_dslxt_success)
			{
			unsigned int vlen = strlen(vpnt)+1;
			char *vcopy = (char *)malloc(vlen);
			strcpy(vcopy, vpnt);
			lt->dict_string_mem_required += vlen;
			lt->dict = lxt2_wr_dslxt_insert(vcopy, lt->dict, lt->num_dict_entries);

			if(lt->dict_curr)
				{
				lt->dict_curr->next = lt->dict;
				lt->dict_curr = lt->dict;
				}
				else
				{
				lt->dict_head =  lt->dict_curr = lt->dict;
				}

			idx = lt->num_dict_entries + LXT2_WR_DICT_START;
			lt->num_dict_entries++;
			}
			else
			{
			idx = lt->dict->val + LXT2_WR_DICT_START;
			}
		}

do_enc:
	if((s->msk & (LXT2_WR_GRAN_1VAL<<lt->timepos)) == LXT2_WR_GRAN_0VAL)
		{
		s->msk |= (LXT2_WR_GRAN_1VAL<<lt->timepos);
		s->chg[s->chgpos] = idx;

		s->chgpos++;
		}
		else
		{
		s->chg[s->chgpos-1] = idx;
		}

	strncpy(s->value, value, s->len);

	lt->granule_dirty = 1;
	}

return(rc);
}


/*
 * dumping control
 */
void lxt2_wr_set_dumpoff(struct lxt2_wr_trace *lt)
{
struct lxt2_wr_symbol *s;

if((lt)&&(!lt->blackout))
	{
	if(!lt->emitted)
	        {
	        lxt2_wr_emitfacs(lt);
	        lt->emitted = 1;

	        if(!lt->timeset)
	                {
	                lxt2_wr_set_time(lt, 0);
	                }
	        }

	s = lt->symchain;
	while(s)
		{
		if(!(s->flags&LXT2_WR_SYM_F_ALIAS))
			{
			if((s->msk & (LXT2_WR_GRAN_1VAL<<lt->timepos)) == LXT2_WR_GRAN_0VAL)
				{
				s->msk |= (LXT2_WR_GRAN_1VAL<<lt->timepos);
				s->chg[s->chgpos] = LXT2_WR_ENC_BLACKOUT;

				s->chgpos++;
				}
				else
				{
				s->chg[s->chgpos-1] = LXT2_WR_ENC_BLACKOUT;
				}
			}

		s=s->symchain;
		}

	lt->bumptime = 1;
	lt->blackout = 1;
	lt->granule_dirty = 1;
	}
}


void lxt2_wr_set_dumpon(struct lxt2_wr_trace *lt)
{
int i;
struct lxt2_wr_symbol *s;

if((lt)&&(lt->blackout))
	{
	lt->blackout = 0;

	s = lt->symchain;
	while(s)
		{
		if(!(s->flags&LXT2_WR_SYM_F_ALIAS))
			{
			if(s->flags&LXT2_WR_SYM_F_DOUBLE)
			        {
				free(s->value);
			        s->value = strdup("0");			/* will cause mismatch then flush */
			        }
			        else
			        {
				if(!(s->flags&LXT2_WR_SYM_F_STRING))
					{
					s->value[0] = '-';		/* will cause mismatch then flush */
				        for(i=1;i<s->len;i++)
				                {
				                s->value[i] = 'x';      /* initial value */
				                }
				        s->value[i]=0;
				        }
					else
					{
					free(s->value);
					s->value = (char*)calloc(1, 1*sizeof(char));
					}
				}
			}

		s=s->symchain;
		}

	s = lt->symchain;
        while(s)
                {
                if((!(s->flags&LXT2_WR_SYM_F_ALIAS))&&(s->rows<2))
                        {
			char tmp[16]; // To get rid of the warning
			if(!(s->flags&(LXT2_WR_SYM_F_DOUBLE|LXT2_WR_SYM_F_STRING)))
				{
	                        strcpy(tmp, "x");
	                        lxt2_wr_emit_value_bit_string(lt, s, 0, tmp);
				}
			else if (s->flags&LXT2_WR_SYM_F_DOUBLE)
				{
				double value;
				sscanf("NaN", "%lg", &value);
				lxt2_wr_emit_value_double(lt, s, 0, value);
				}
			else if (s->flags&LXT2_WR_SYM_F_STRING)
				{
				strcpy(tmp, "UNDEF");
				lxt2_wr_emit_value_string(lt, s, 0, tmp);
				}
                        }
                s=s->symchain;
                }
	}
}


/*
 * flush the trace...
 */
void lxt2_wr_flush(struct lxt2_wr_trace *lt)
{
if(lt)
	{
	if((lt->timegranule)||(lt->timepos > 0))
		{
		if(lt->granule_dirty)
			{
			lt->timepos++;
			lxt2_wr_flush_granule(lt, 1);
			}
		}
	}
}


/*
 * close out the trace and fixate it
 */
void lxt2_wr_close(struct lxt2_wr_trace *lt)
{
if(lt)
	{
	if(lt->granule_dirty)
		{
		lt->timepos++;
		lxt2_wr_flush_granule(lt, 1);
		}

	if(lt->symchain)
		{
		struct lxt2_wr_symbol *s = lt->symchain;
		struct lxt2_wr_symbol *s2;

		while(s)
			{
			free(s->name);
			free(s->value);
			s2=s->symchain;
			free(s);
			s=s2;
			}

		lt->symchain=NULL;
		}

	free(lt->lxtname);
	free(lt->sorted_facs);
	fclose(lt->handle);
	free(lt);
	}

}

/*
 * set compression depth
 */
void lxt2_wr_set_compression_depth(struct lxt2_wr_trace *lt, unsigned int depth)
{
if(lt)
	{
	if(depth > 9) depth = 9;
	sprintf(lt->zmode, "wb%u", depth);
	}
}


/*
 * time zero offset
 */
void lxt2_wr_set_timezero(struct lxt2_wr_trace *lt, lxtstime_t timeval)
{
if(lt)
        {
        lt->timezero = timeval;
        }
}
