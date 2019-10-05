#ifndef TAINT_HEADER
#define TAINT_HEADER
#define TaintPropogateSig4(a,b,c,d,y) \
	y.SetTaint(max(max(max(a.GetTaint(),b.GetTaint()),c.GetTaint()),d.GetTaint()));

#define TaintPropogateSig3(a,b,c,y) \
	y.SetTaint(max(max(a.GetTaint(),b.GetTaint()),c.GetTaint()));\
	if(a.GetTaint()|| b.GetTaint()|| c.GetTaint()) log("### taint=1 %s %s %s###\n",log_signal(a), log_signal(b),log_signal(c));


#define TaintPropogateSig2(a,b,y) \
	y.SetTaint(max(a.GetTaint(),b.GetTaint()));\
	if(a.GetTaint()|| b.GetTaint()) log("### taint=1 %s %s ###\n",log_signal(a), log_signal(b));\


#define TaintPropogateSig1(a,y) \
	y.SetTaint(a.GetTaint());\
	if(a.GetTaint()) log("### taint=1 %s ###\n",log_signal(a));

#endif
