FROM daewok/sbcl:2.2.0-alpine3.15

WORKDIR /opt/app

COPY *.lisp ./
COPY run.sh .

RUN chmod +x run.sh

ENTRYPOINT [ "./run.sh" ]
