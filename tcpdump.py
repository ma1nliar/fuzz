import random
import re
import os
import string
target="Usage: tcpdump [-aAbdDefhHIJKlLnNOpqStuUvxX#] [ -B size ] [ -c count ][ -C file_size ] [ -E algo:secret ] [ -F file ] [ -G seconds ][ -i interface ] [ -j tstamptype ] [ -M secret ] [ --number ][ -Q in|out|inout ][ -r file ] [ -s snaplen ] [ --time-stamp-precision precision ][ --immediate-mode ] [ -T type ] [ --version ] [ -V file ][ -w file ] [ -W filecount ] [ -y datalinktype ] [ -z postrotate"
dict={"-B":"size",}


chars = string.ascii_letters
def random_string_generator(str_size, allowed_chars):
    return ''.join(random.choice(allowed_chars) for x in range(str_size))


def config():
    #res=re.findall(r"^-.w.s.w.s$",target)
        res = re.findall("-\w*\s*\w*\s", target)
    #print(res)

        dict={}
        configlist=""
        for item in res:

            l=item.split()
            a=len(l)

            if a==2:
            #print(l[1])
                print(l[0])
                print(l[1])
                if l[1].find("size")!=-1 or l[0].find("size")!=-1 or l[1].find("count")!=-1 or l[0].find("count")!=-1:
                    a=random.randint(1,100)
                    l[1]=a
                    config = ""
                    config=config.join(l[0])

                    configlist=configlist+' '+config+' '+str(a)
                    #print(config)
                #print(l)
                elif l[1].find("file")!=-1:
                    b=os.getcwd()
                    config = ""
                    config = config.join(l[0])
                    pathdir=os.listdir(b)
                    path=[]

                    sample=random.sample(pathdir,1)
                    #print(sample)
                    #print(b)
                    con=' '.join(l[0])
                    config=' '.join(sample)

                    div=b+"\\"+config
                    #print(b)
                    #print(config)
                    #print(div)
                    configlist=configlist+' '+con+' '+div


                else:
                    n=random_string_generator(8, chars)
                    #print(l[0])
                    con = ''.join(l[0])
                    configlist=configlist+' '+con+' '+n
        return configlist
    #print(os.getcwd())


if __name__=="__main__":



    with open("23.txt", "a") as f:
        for i in range(10):
            m="tcpdump"
            m=m+config()
            print(m)
            f.write(m)
            f.write("\n")
        #dict[q[0]]=q[1]
    #print(dict)