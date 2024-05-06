create table session_temp(
    id integer primary key,
    token text not null unique,
    csrf_token text not null unique,
    user_id int references user(id) on delete cascade not null
);

insert into
    session_temp
select
    *
from
    session;

drop table session;

alter table
    session_temp rename to session;

create table user_invitation(
    id integer primary key,
    token text not null unique,
    created_at datetime not null
);